-- Prove2me | solution 1 for Module.exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/765761cd-ec26-5048-8e8c-b87cdda10fd4

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex

set_option autoImplicit false

universe u

open TensorProduct

namespace P2mMumfordKerModel

section Generalities

variable {R : Type u} [CommRing R]

theorem flat_prod (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro Q P _ _ _ _ f hf
  have key : (TensorProduct.prodLeft R R M N P).toLinearMap ∘ₗ LinearMap.lTensor (M × N) f =
      LinearMap.prodMap (LinearMap.lTensor M f) (LinearMap.lTensor N f) ∘ₗ
        (TensorProduct.prodLeft R R M N Q).toLinearMap := by
    apply TensorProduct.ext'
    rintro ⟨a1, a2⟩ b
    simp
  have hM := Module.Flat.lTensor_preserves_injective_linearMap (M := M) f hf
  have hN := Module.Flat.lTensor_preserves_injective_linearMap (M := N) f hf
  intro x y hxy
  have kx := LinearMap.congr_fun key x
  have ky := LinearMap.congr_fun key y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at kx ky
  have h : (LinearMap.prodMap (LinearMap.lTensor M f) (LinearMap.lTensor N f))
      (TensorProduct.prodLeft R R M N Q x) =
      (LinearMap.prodMap (LinearMap.lTensor M f) (LinearMap.lTensor N f))
      (TensorProduct.prodLeft R R M N Q y) := by
    rw [← kx, ← ky, hxy]
  rw [LinearMap.prodMap_apply, LinearMap.prodMap_apply, Prod.mk.injEq] at h
  exact (TensorProduct.prodLeft R R M N Q).injective (Prod.ext (hM h.1) (hN h.2))

theorem flat_ker_of_surjective {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P]
    [Module R P] [Module.Flat R M] [Module.Flat R P] (f : M →ₗ[R] P)
    (hf : Function.Surjective f) : Module.Flat R (LinearMap.ker f) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ i hi
  have h1 : Function.Injective (LinearMap.lTensor N (LinearMap.ker f).subtype) :=
    LinearMap.lTensor_injective_of_exact_of_flat f hf _ (LinearMap.ker f).injective_subtype
      (f.exact_subtype_ker_map) N
  have h2 : Function.Injective (LinearMap.rTensor M i) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hi
  have hcomp : (LinearMap.rTensor M i) ∘ₗ (LinearMap.lTensor N (LinearMap.ker f).subtype) =
      (LinearMap.lTensor N' (LinearMap.ker f).subtype) ∘ₗ
        (LinearMap.rTensor (LinearMap.ker f) i) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have h3 : Function.Injective ((LinearMap.lTensor N' (LinearMap.ker f).subtype) ∘ₗ
      (LinearMap.rTensor (LinearMap.ker f) i)) := by
    rw [← hcomp]
    exact h2.comp h1
  exact Function.Injective.of_comp h3

variable {A : Type u} [CommRing A] [Algebra R A]

theorem eq_zero_of_fst_snd_baseChange {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (z : A ⊗[R] (M × N))
    (h1 : (LinearMap.fst R M N).baseChange A z = 0)
    (h2 : (LinearMap.snd R M N).baseChange A z = 0) : z = 0 := by
  have hid : LinearMap.inl R M N ∘ₗ LinearMap.fst R M N + LinearMap.inr R M N ∘ₗ LinearMap.snd R M N
      = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨m, n'⟩
    simp
  have h := congrArg (fun f : (M × N) →ₗ[R] (M × N) => f.baseChange A z) hid
  simp only [LinearMap.baseChange_add, LinearMap.baseChange_comp, LinearMap.baseChange_id,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, h1, h2, map_zero,
    add_zero] at h
  exact h.symm

theorem inl_baseChange_injective (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    Function.Injective ((LinearMap.inl R M N).baseChange A) := by
  refine Function.LeftInverse.injective (g := (LinearMap.fst R M N).baseChange A) fun x => ?_
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.fst_comp_inl,
    LinearMap.baseChange_id, LinearMap.id_apply]

theorem ker_baseChange_comp_eq {M N P : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hg : Function.Injective (g.baseChange A)) :
    LinearMap.ker ((g ∘ₗ f).baseChange A) = LinearMap.ker (f.baseChange A) := by
  rw [LinearMap.baseChange_comp]
  exact LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hg)

theorem subtype_baseChange_injective {M K : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K] [Module.Flat R K] (σ : M →ₗ[R] K)
    (hσ : Function.Surjective σ) :
    Function.Injective ((LinearMap.ker σ).subtype.baseChange A) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_injective_of_exact_of_flat σ hσ _ (LinearMap.ker σ).injective_subtype
    (σ.exact_subtype_ker_map) A

theorem subtype_baseChange_exact {M K : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K] (σ : M →ₗ[R] K) (hσ : Function.Surjective σ) :
    Function.Exact ((LinearMap.ker σ).subtype.baseChange A) (σ.baseChange A) := by
  rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
  exact lTensor_exact A (σ.exact_subtype_ker_map) hσ

omit [Algebra R A] in

theorem exists_coprod_surjective {M K : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K] (e : M →ₗ[R] K)
    [Module.Finite R (K ⧸ LinearMap.range e)] :
    ∃ (m : ℕ) (g : (Fin m → R) →ₗ[R] K), Function.Surjective (e.coprod g) := by
  obtain ⟨m, g', hg'⟩ := Module.Finite.exists_fin' R (K ⧸ LinearMap.range e)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (LinearMap.range e).mkQ g'
    (Submodule.mkQ_surjective _)
  refine ⟨m, g, fun y => ?_⟩
  obtain ⟨r, hr⟩ := hg' ((LinearMap.range e).mkQ y)
  have h : (LinearMap.range e).mkQ (g r) = (LinearMap.range e).mkQ y := by
    rw [← LinearMap.comp_apply, hg, hr]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp h
  refine ⟨(-c, r), ?_⟩
  rw [LinearMap.coprod_apply, map_neg, hc]
  abel

end Generalities

section Ext

variable {R : Type u} [CommRing R]
variable {M K : Type u} [AddCommGroup M] [Module R M] [AddCommGroup K] [Module R K]
variable (e : M →ₗ[R] K) {m : ℕ} (g : (Fin m → R) →ₗ[R] K)

abbrev Kx : Submodule R (M × (Fin m → R)) := LinearMap.ker (e.coprod g)

theorem mem_Kx_iff (x : M × (Fin m → R)) : x ∈ Kx e g ↔ e x.1 + g x.2 = 0 := by
  rw [LinearMap.mem_ker, LinearMap.coprod_apply]

theorem inl_mem_Kx_iff (c : M) : LinearMap.inl R M (Fin m → R) c ∈ Kx e g ↔ e c = 0 := by
  rw [mem_Kx_iff, LinearMap.inl_apply, map_zero, add_zero]

def φ₀ : Kx e g →ₗ[R] M := LinearMap.fst R M (Fin m → R) ∘ₗ (Kx e g).subtype

def δ : Kx e g →ₗ[R] (Fin m → R) := LinearMap.snd R M (Fin m → R) ∘ₗ (Kx e g).subtype

@[scoped simp] theorem φ₀_apply (k : Kx e g) : φ₀ e g k = (k : M × (Fin m → R)).1 := rfl
@[scoped simp] theorem δ_apply (k : Kx e g) : δ e g k = (k : M × (Fin m → R)).2 := rfl

theorem e_comp_φ₀ : e ∘ₗ φ₀ e g = (-g) ∘ₗ δ e g := by
  ext k
  have hk := (mem_Kx_iff e g k).mp k.2
  simp only [LinearMap.comp_apply, φ₀_apply, δ_apply, LinearMap.neg_apply]
  rw [eq_neg_iff_add_eq_zero, hk]

theorem flat_Kx [Module.Flat R M] [Module.Flat R K] (hσ : Function.Surjective (e.coprod g)) :
    Module.Flat R (Kx e g) := by
  haveI : Module.Flat R (M × (Fin m → R)) := flat_prod _ _
  exact flat_ker_of_surjective _ hσ

theorem Kx_inf_ker_snd :
    Kx e g ⊓ LinearMap.ker (LinearMap.snd R M (Fin m → R)) =
      (LinearMap.ker e).map (LinearMap.inl R M (Fin m → R)) := by
  ext ⟨c, r⟩
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map,
    LinearMap.inl_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨c, ?_, rfl, rfl⟩
    rw [LinearMap.coprod_apply, map_zero, add_zero] at h
    exact h
  · rintro ⟨c', hc', rfl, rfl⟩
    refine ⟨?_, rfl⟩
    rw [LinearMap.coprod_apply, map_zero, add_zero]
    exact hc'

theorem fg_Kx [IsNoetherianRing R] (hfin : Module.Finite R (LinearMap.ker e)) : (Kx e g).FG := by
  apply Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd R M (Fin m → R))
  · exact IsNoetherian.noetherian _
  · rw [Kx_inf_ker_snd]
    exact (Module.Finite.iff_fg.mp hfin).map _

variable {A : Type u} [CommRing A] [Algebra R A]

theorem eq_zero_of_δ_φ₀ [Module.Flat R K] (hσ : Function.Surjective (e.coprod g))
    (x : A ⊗[R] Kx e g) (hδ : (δ e g).baseChange A x = 0) (hφ : (φ₀ e g).baseChange A x = 0) :
    x = 0 := by
  apply subtype_baseChange_injective (e.coprod g) hσ
  rw [map_zero]
  apply eq_zero_of_fst_snd_baseChange
  · rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    exact hφ
  · rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    exact hδ

theorem exists_of_baseChange_eq_zero (hσ : Function.Surjective (e.coprod g))
    (y : A ⊗[R] M) (hy : e.baseChange A y = 0) :
    ∃ x : A ⊗[R] Kx e g, (δ e g).baseChange A x = 0 ∧ (φ₀ e g).baseChange A x = y := by
  have hz : (e.coprod g).baseChange A ((LinearMap.inl R M (Fin m → R)).baseChange A y) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.coprod_inl, hy]
  obtain ⟨x, hx⟩ := (subtype_baseChange_exact (A := A) (e.coprod g) hσ _).mp hz
  refine ⟨x, ?_, ?_⟩
  · change ((LinearMap.snd R M (Fin m → R)) ∘ₗ (Kx e g).subtype).baseChange A x = 0
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply, hx, ← LinearMap.comp_apply,
      ← LinearMap.baseChange_comp, LinearMap.snd_comp_inl, LinearMap.baseChange_zero,
      LinearMap.zero_apply]
  · change ((LinearMap.fst R M (Fin m → R)) ∘ₗ (Kx e g).subtype).baseChange A x = y
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply, hx, ← LinearMap.comp_apply,
      ← LinearMap.baseChange_comp, LinearMap.fst_comp_inl, LinearMap.baseChange_id,
      LinearMap.id_apply]

variable {M₀ : Type u} [AddCommGroup M₀] [Module R M₀] (d₀ : M₀ →ₗ[R] M) (hed : ∀ x, e (d₀ x) = 0)

def e' : M₀ →ₗ[R] Kx e g :=
  LinearMap.codRestrict (Kx e g) (LinearMap.inl R M (Fin m → R) ∘ₗ d₀) fun x =>
    (inl_mem_Kx_iff e g _).mpr (hed x)

theorem e'_val (x : M₀) : ((e' e g d₀ hed x : Kx e g) : M × (Fin m → R)) = (d₀ x, 0) := rfl

theorem subtype_comp_e' : (Kx e g).subtype ∘ₗ e' e g d₀ hed = LinearMap.inl R M (Fin m → R) ∘ₗ d₀ :=
  LinearMap.subtype_comp_codRestrict _ _ _

theorem φ₀_comp_e' : φ₀ e g ∘ₗ e' e g d₀ hed = d₀ := by
  ext x
  rfl

theorem ker_e' : LinearMap.ker (e' e g d₀ hed) = LinearMap.ker d₀ := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    have h' := congrArg (fun k : Kx e g => (k : M × (Fin m → R)).1) h
    simpa [e'_val] using h'
  · intro h
    apply Subtype.ext
    rw [e'_val, h]
    rfl

theorem ker_baseChange_e' [Module.Flat R K] (hσ : Function.Surjective (e.coprod g)) :
    LinearMap.ker ((e' e g d₀ hed).baseChange A) = LinearMap.ker (d₀.baseChange A) := by
  have hinj : Function.Injective ((Kx e g).subtype.baseChange A) :=
    subtype_baseChange_injective (e.coprod g) hσ
  have h1 := ker_baseChange_comp_eq (A := A) (e' e g d₀ hed) (Kx e g).subtype hinj
  rw [subtype_comp_e'] at h1
  rw [← h1]
  exact ker_baseChange_comp_eq _ _ (inl_baseChange_injective _ _)

theorem finite_coker_e' [IsNoetherianRing R] (N : Submodule R M) (hN : LinearMap.ker e = N)
    (hfin : Module.Finite R (N ⧸ (LinearMap.range d₀).comap N.subtype)) :
    Module.Finite R (Kx e g ⧸ LinearMap.range (e' e g d₀ hed)) := by
  have hle : LinearMap.range (e' e g d₀ hed) ≤
      LinearMap.ker (LinearMap.snd R M (Fin m → R) ∘ₗ (Kx e g).subtype) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, e'_val]
    rfl
  let f : (Kx e g ⧸ LinearMap.range (e' e g d₀ hed)) →ₗ[R] (Fin m → R) :=
    (LinearMap.range (e' e g d₀ hed)).liftQ (LinearMap.snd R M (Fin m → R) ∘ₗ (Kx e g).subtype) hle
  have hmemN : ∀ c : N, LinearMap.inl R M (Fin m → R) (c : M) ∈ Kx e g := fun c => by
    rw [inl_mem_Kx_iff]
    have : (c : M) ∈ LinearMap.ker e := by rw [hN]; exact c.2
    exact this
  let ψ₀ : N →ₗ[R] (Kx e g ⧸ LinearMap.range (e' e g d₀ hed)) :=
    (LinearMap.range (e' e g d₀ hed)).mkQ ∘ₗ
      LinearMap.codRestrict (Kx e g) (LinearMap.inl R M (Fin m → R) ∘ₗ N.subtype) hmemN
  have hψ₀ : (LinearMap.range d₀).comap N.subtype ≤ LinearMap.ker ψ₀ := by
    intro c hc
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hc
    rw [LinearMap.mem_ker]
    change (LinearMap.range (e' e g d₀ hed)).mkQ _ = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨x, Subtype.ext ?_⟩
    rw [e'_val]
    change (d₀ x, (0 : Fin m → R)) = LinearMap.inl R M (Fin m → R) (N.subtype c)
    rw [hx, LinearMap.inl_apply]
  have hrange : (LinearMap.range ψ₀).FG := by
    haveI := hfin
    rw [← Submodule.range_liftQ _ ψ₀ hψ₀]
    exact Module.Finite.iff_fg.mp inferInstance
  have hker : LinearMap.ker f = LinearMap.range ψ₀ := by
    apply le_antisymm
    · intro q hq
      obtain ⟨k, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (e' e g d₀ hed)) q
      obtain ⟨⟨c, r⟩, hk⟩ := k
      have hr : r = 0 := by
        rw [LinearMap.mem_ker] at hq
        exact hq
      subst hr
      have hc : c ∈ N := by
        rw [← hN]
        exact (inl_mem_Kx_iff e g c).mp hk
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro _ ⟨c, rfl⟩
      rw [LinearMap.mem_ker]
      change f ((LinearMap.range (e' e g d₀ hed)).mkQ _) = 0
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
      rfl
  have htop : (⊤ : Submodule R (Kx e g ⧸ LinearMap.range (e' e g d₀ hed))).FG := by
    apply Submodule.fg_of_fg_map_of_fg_inf_ker f
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq, hker]
      exact hrange
  exact Module.finite_def.mpr htop

end Ext

section Truncation

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {C : ℕ → Type u} [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  [∀ i, Module.Flat R (C i)]
variable (d : ∀ i, C i →ₗ[R] C (i + 1))

structure Trunc (p : ℕ) : Type (u + 1) where

  K : Type u
  [acg : AddCommGroup K]
  [mod : Module R K]
  [flat : Module.Flat R K]

  e : C p →ₗ[R] K

  ι : K →ₗ[R] C (p + 1)
  ι_comp : ι ∘ₗ e = d p
  ker_eq : LinearMap.ker e = LinearMap.ker (d p)
  ker_bc : ∀ (A : Type u) [CommRing A] [Algebra R A],
    LinearMap.ker (e.baseChange A) = LinearMap.ker ((d p).baseChange A)
  fin : Module.Finite R (K ⧸ LinearMap.range e)

attribute [scoped instance] Trunc.acg Trunc.mod Trunc.flat

variable {d}

def truncBase (p : ℕ) [Subsingleton (C (p + 1))] : Trunc d p where
  K := C (p + 1)
  e := d p
  ι := LinearMap.id
  ι_comp := LinearMap.id_comp _
  ker_eq := rfl
  ker_bc _ _ _ := rfl
  fin := inferInstance

theorem truncStep (p : ℕ) (hdd : d (p + 1) ∘ₗ d p = 0)
    (hfin : Module.Finite R (LinearMap.ker (d (p + 1)) ⧸
      (LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype))
    (T : Trunc d (p + 1)) : Nonempty (Trunc d p) := by
  haveI := T.fin
  obtain ⟨m, g, hσ⟩ := exists_coprod_surjective T.e
  have hed : ∀ x : C p, T.e (d p x) = 0 := fun x => by
    have h1 : d p x ∈ LinearMap.ker (d (p + 1)) := by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hdd, LinearMap.zero_apply]
    rw [← T.ker_eq] at h1
    exact h1
  haveI : Module.Flat R (Kx T.e g) := flat_Kx T.e g hσ
  exact ⟨{
    K := Kx T.e g
    e := e' T.e g (d p) hed
    ι := φ₀ T.e g
    ι_comp := φ₀_comp_e' T.e g (d p) hed
    ker_eq := ker_e' T.e g (d p) hed
    ker_bc := fun A _ _ => ker_baseChange_e' T.e g (d p) hed hσ
    fin := finite_coker_e' T.e g (d p) hed (LinearMap.ker (d (p + 1))) T.ker_eq hfin }⟩

theorem trunc_all (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∀ j p : ℕ, n ≤ p + j → Nonempty (Trunc d p) := by
  intro j
  induction j with
  | zero =>
      intro p hp
      haveI : Subsingleton (C (p + 1)) := hbdd _ (by omega)
      exact ⟨truncBase p⟩
  | succ j ih =>
      intro p hp
      by_cases h : n ≤ p
      · haveI : Subsingleton (C (p + 1)) := hbdd _ (by omega)
        exact ⟨truncBase p⟩
      · obtain ⟨T⟩ := ih (p + 1) (by omega)
        exact truncStep p (hdd p) (hfin p) T

theorem exists_trunc_zero (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (n : ℕ)
    (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    Nonempty (Trunc d 0) :=
  trunc_all hdd n hbdd hfin n 0 (by omega)

end Truncation

section Model

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {C : ℕ → Type u} [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  [∀ i, Module.Flat R (C i)]
variable {d : ∀ i, C i →ₗ[R] C (i + 1)}

theorem exists_model (T : Trunc d 0) (hfin0 : Module.Finite R (LinearMap.ker (d 0))) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C 0) (ι1 : G.C1 →ₗ[R] C 1)
      (comm : d 0 ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerMapBaseChange G.d (d 0) ι0 ι1 comm A) := by
  haveI := T.fin
  obtain ⟨m, g, hσ⟩ := exists_coprod_surjective T.e

  haveI hflat : Module.Flat R (Kx T.e g) := flat_Kx T.e g hσ
  have hker0 : Module.Finite R (LinearMap.ker T.e) := by rw [T.ker_eq]; exact hfin0
  haveI hfinK : Module.Finite R (Kx T.e g) := Module.Finite.iff_fg.mpr (fg_Kx T.e g hker0)
  haveI : Module.FinitePresentation R (Kx T.e g) := Module.finitePresentation_of_finite R _
  haveI hproj : Module.Projective R (Kx T.e g) := Module.Flat.projective_of_finitePresentation

  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' R (Kx T.e g)
  obtain ⟨i, hsi⟩ := Module.projective_lifting_property s LinearMap.id hs

  let dG : (Fin n → R) →ₗ[R] ((Fin m → R) × (Fin n → R)) :=
    LinearMap.prod (δ T.e g ∘ₗ s) (LinearMap.id - i ∘ₗ s)
  let G : CoherentBaseChange.TwoTermComplex.{u, u} R :=
    { C0 := Fin n → R, C1 := (Fin m → R) × (Fin n → R), d := dG }
  let ι0 : (Fin n → R) →ₗ[R] C 0 := φ₀ T.e g ∘ₗ s
  let ι1 : ((Fin m → R) × (Fin n → R)) →ₗ[R] C 1 := (T.ι ∘ₗ (-g)) ∘ₗ LinearMap.fst R _ _
  have hcomm : d 0 ∘ₗ ι0 = ι1 ∘ₗ dG := by
    change d 0 ∘ₗ (φ₀ T.e g ∘ₗ s) = ((T.ι ∘ₗ (-g)) ∘ₗ LinearMap.fst R _ _) ∘ₗ
      LinearMap.prod (δ T.e g ∘ₗ s) (LinearMap.id - i ∘ₗ s)
    rw [LinearMap.comp_assoc, LinearMap.fst_prod, ← LinearMap.comp_assoc, ← T.ι_comp]
    simp only [LinearMap.comp_assoc]
    congr 1
    rw [← LinearMap.comp_assoc, e_comp_φ₀, LinearMap.comp_assoc]
  refine ⟨G, ι0, ι1, hcomm, fun A _ _ => ?_⟩

  have hfst : LinearMap.fst R _ _ ∘ₗ dG = δ T.e g ∘ₗ s := LinearMap.fst_prod _ _
  have hsnd : LinearMap.snd R _ _ ∘ₗ dG = LinearMap.id - i ∘ₗ s := LinearMap.snd_prod _ _
  have hval : ∀ x, ((TwoChartCech.kerMapBaseChange G.d (d 0) ι0 ι1 hcomm A x :
      LinearMap.ker ((d 0).baseChange A)) : A ⊗[R] C 0) = (φ₀ T.e g).baseChange A (s.baseChange A x) := by
    intro x
    change ι0.baseChange A x = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  constructor
  ·
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx0 : (φ₀ T.e g).baseChange A (s.baseChange A x) = 0 := by
      rw [← hval, hx]
      rfl
    have hxker : dG.baseChange A (x : A ⊗[R] (Fin n → R)) = 0 := x.2
    have hδ : (δ T.e g).baseChange A (s.baseChange A x) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← hfst, LinearMap.baseChange_comp,
        LinearMap.comp_apply, hxker, map_zero]
    have hsx : s.baseChange A x = 0 := eq_zero_of_δ_φ₀ T.e g hσ _ hδ hx0
    have hx2 : (LinearMap.id - i ∘ₗ s).baseChange A (x : A ⊗[R] (Fin n → R)) = 0 := by
      rw [← hsnd, LinearMap.baseChange_comp, LinearMap.comp_apply, hxker, map_zero]
    rw [LinearMap.baseChange_sub, LinearMap.sub_apply, LinearMap.baseChange_id, LinearMap.id_apply,
      LinearMap.baseChange_comp, LinearMap.comp_apply, hsx, map_zero, sub_zero] at hx2
    exact Subtype.ext hx2
  ·
    intro y
    obtain ⟨w, hwδ, hwφ⟩ := exists_of_baseChange_eq_zero T.e g hσ (A := A) (y : A ⊗[R] C 0)
      (by
        have hy : (y : A ⊗[R] C 0) ∈ LinearMap.ker (T.e.baseChange A) := by
          rw [T.ker_bc]; exact y.2
        exact hy)
    have hsiw : s.baseChange A (i.baseChange A w) = w := by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hsi, LinearMap.baseChange_id,
        LinearMap.id_apply]
    have hmem : i.baseChange A w ∈ LinearMap.ker (dG.baseChange A) := by
      rw [LinearMap.mem_ker]
      apply eq_zero_of_fst_snd_baseChange
      · rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hfst, LinearMap.baseChange_comp,
          LinearMap.comp_apply, hsiw, hwδ]
      · rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hsnd, LinearMap.baseChange_sub,
          LinearMap.sub_apply, LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.baseChange_comp,
          LinearMap.comp_apply, hsiw, sub_self]
    refine ⟨⟨i.baseChange A w, hmem⟩, Subtype.ext ?_⟩
    rw [hval]
    change (φ₀ T.e g).baseChange A (s.baseChange A (i.baseChange A w)) = (y : A ⊗[R] C 0)
    rw [hsiw, hwφ]

end Model

theorem main
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C 0) (ι1 : G.C1 →ₗ[R] C 1)
      (comm : d 0 ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerMapBaseChange G.d (d 0) ι0 ι1 comm A) := by
  obtain ⟨T⟩ := exists_trunc_zero (d := d) hdd n hbdd hfin
  exact exists_model T hfin0

theorem main_trunc
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ (K : Type u) (_ : AddCommGroup K) (_ : Module R K) (_ : Module.Flat R K)
      (e : C 0 →ₗ[R] K) (ι : K →ₗ[R] C 1),
      ι ∘ₗ e = d 0 ∧ LinearMap.ker e = LinearMap.ker (d 0) ∧
      Module.Finite R (K ⧸ LinearMap.range e) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        LinearMap.ker (e.baseChange A) = LinearMap.ker ((d 0).baseChange A) := by
  obtain ⟨T⟩ := exists_trunc_zero (d := d) hdd n hbdd hfin
  exact ⟨T.K, T.acg, T.mod, T.flat, T.e, T.ι, T.ι_comp, T.ker_eq, T.fin, fun A _ _ => T.ker_bc A⟩

end P2mMumfordKerModel
p2m_reactivate "P2MW.S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex.P2mMumfordKerModel"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C 0) (ι1 : G.C1 →ₗ[R] C 1)
      (comm : d 0 ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerMapBaseChange G.d (d 0) ι0 ι1 comm A) :=
  P2mMumfordKerModel.main R C d hdd n hbdd hfin0 hfin

end S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex
end P2MW
export P2MW.S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex (solution)
