-- Prove2me | solution 1 for Module.exists_ideal_forall_projective_and_rankAtStalk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/16579c9a-f42b-5adf-9ddc-c5e78d387ab3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_ideal_forall_projective_and_rankAtStalk_eq_iff

set_option autoImplicit false

open scoped TensorProduct
open TensorProduct

namespace FittingClosed

section Modules

variable {A : Type} [CommRing A]

theorem exists_equiv_prod_ker {Q₁ Q₂ : Type} [AddCommGroup Q₁] [Module A Q₁] [AddCommGroup Q₂] [Module A Q₂]
    [Module.Projective A Q₂] (π : Q₁ →ₗ[A] Q₂) (hπ : Function.Surjective π) :
    ∃ e : Q₁ ≃ₗ[A] Q₂ × LinearMap.ker π, ∀ x, (e x).1 = π x := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hs' : ∀ y, π (s y) = y := fun y => by simpa using LinearMap.congr_fun hs y
  refine ⟨{ toFun := fun x => (π x, ⟨x - s (π x), by simp [hs']⟩)
            invFun := fun yk => s yk.1 + yk.2
            map_add' := fun x y => by ext <;> simp [map_add]; abel
            map_smul' := fun a x => by ext <;> simp [map_smul, smul_sub]
            left_inv := fun x => by simp
            right_inv := fun yk => by
              obtain ⟨y, k, hk⟩ := yk
              have hk' : π k = 0 := hk
              ext <;> simp [hs', hk'] }, fun x => rfl⟩

theorem nontrivial_of_primeSpectrum (q : PrimeSpectrum A) : Nontrivial A :=
  not_subsingleton_iff_nontrivial.mp fun _ => (IsEmpty.false q)

end Modules

section Core

variable {A : Type} [CommRing A] {M : Type} [AddCommGroup M] [Module A M] {r : ℕ}

def syz (ε : (Fin r → A) →ₗ[A] M) : Ideal A :=
  ⨆ i : Fin r, (LinearMap.ker ε).map (LinearMap.proj i)

theorem apply_mem_syz (ε : (Fin r → A) →ₗ[A] M) {k : Fin r → A} (hk : ε k = 0) (i : Fin r) :
    k i ∈ syz ε := by
  refine Submodule.mem_iSup_of_mem i ?_
  exact Submodule.mem_map_of_mem (f := LinearMap.proj i) (LinearMap.mem_ker.mpr hk)

theorem syz_le_iff (ε : (Fin r → A) →ₗ[A] M) (J : Ideal A) :
    syz ε ≤ J ↔ ∀ k : Fin r → A, ε k = 0 → ∀ i, k i ∈ J := by
  constructor
  · intro h k hk i
    exact h (apply_mem_syz ε hk i)
  · intro h
    refine iSup_le fun i => ?_
    rintro _ ⟨k, hk, rfl⟩
    exact h k (LinearMap.mem_ker.mp hk) i

variable (C : Type) [CommRing C] [Algebra A C]

theorem piScalarRight_tmul (c : C) (k : Fin r → A) :
    piScalarRight A C C (Fin r) (c ⊗ₜ[A] k) = fun i => algebraMap A C (k i) * c := by
  classical
  rw [piScalarRight_apply, piScalarRightHom_tmul]
  funext i
  rw [Algebra.smul_def]

theorem core_equiv (ε : (Fin r → A) →ₗ[A] M) (hε : Function.Surjective ε)
    (h : ∀ a ∈ syz ε, algebraMap A C a = 0) :
    ∃ e : (C ⊗[A] M) ≃ₗ[C] (Fin r → C),
      ∀ k : Fin r → A, e ((1 : C) ⊗ₜ[A] ε k) = fun i => algebraMap A C (k i) := by
  classical
  set g : C ⊗[A] (Fin r → A) →ₗ[C] C ⊗[A] M := ε.baseChange C with hg
  have hgs : Function.Surjective g := by
    rw [hg, LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective C hε

  have hex : Function.Exact ((LinearMap.ker ε).subtype.lTensor C) (ε.lTensor C) :=
    lTensor_exact C (LinearMap.exact_subtype_ker_map ε) hε
  have hzero : (LinearMap.ker ε).subtype.lTensor C = 0 := by
    apply TensorProduct.ext'
    intro c k
    rw [LinearMap.lTensor_tmul, LinearMap.zero_apply]
    apply (piScalarRight A C C (Fin r)).injective
    rw [map_zero, piScalarRight_tmul]
    funext i
    rw [Pi.zero_apply, Submodule.subtype_apply, h _ (apply_mem_syz ε (LinearMap.mem_ker.mp k.2) i), zero_mul]
  have hgi : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' : (ε.lTensor C) x = 0 := by
      rw [← LinearMap.baseChange_eq_ltensor]; exact hx
    obtain ⟨y, hy⟩ := (hex x).mp hx'
    rw [← hy, hzero, LinearMap.zero_apply]
  let E : C ⊗[A] (Fin r → A) ≃ₗ[C] C ⊗[A] M := LinearEquiv.ofBijective g ⟨hgi, hgs⟩
  refine ⟨E.symm ≪≫ₗ piScalarRight A C C (Fin r), fun k => ?_⟩
  have hk : E ((1 : C) ⊗ₜ[A] k) = (1 : C) ⊗ₜ[A] ε k := by
    change g ((1 : C) ⊗ₜ[A] k) = _
    rw [hg, LinearMap.baseChange_tmul]
  rw [LinearEquiv.trans_apply, ← hk, LinearEquiv.symm_apply_apply, piScalarRight_tmul]
  funext i
  rw [mul_one]

theorem core_vanish (ε : (Fin r → A) →ₗ[A] M) (hε : Function.Surjective ε)
    [Module.Projective C (C ⊗[A] M)] (hrank : ∀ q : PrimeSpectrum C, Module.rankAtStalk (C ⊗[A] M) q = r) :
    ∀ a ∈ syz ε, algebraMap A C a = 0 := by
  classical
  change syz ε ≤ RingHom.ker (algebraMap A C)
  rw [syz_le_iff]
  intro k hk i
  rw [RingHom.mem_ker]
  rcases subsingleton_or_nontrivial C with hC | hC
  · exact Subsingleton.elim _ _
  set g : C ⊗[A] (Fin r → A) →ₗ[C] C ⊗[A] M := ε.baseChange C with hg
  have hgs : Function.Surjective g := by
    rw [hg, LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective C hε
  haveI : Module.Finite A M := Module.Finite.of_surjective ε hε
  haveI : Module.Finite C (C ⊗[A] M) := Module.Finite.base_change A C M
  haveI : Module.Finite C (C ⊗[A] (Fin r → A)) := Module.Finite.base_change A C _
  obtain ⟨E, hE⟩ := exists_equiv_prod_ker g hgs

  haveI : Module.Finite C (LinearMap.ker g) :=
    Module.Finite.of_surjective ((LinearMap.snd C _ _).comp E.toLinearMap) fun x => ⟨E.symm (0, x), by simp⟩
  haveI : Module.Projective C (LinearMap.ker g) :=
    Module.Projective.of_split (E.symm.toLinearMap.comp (LinearMap.inr C _ _))
      ((LinearMap.snd C _ _).comp E.toLinearMap) (by ext x; simp)
  haveI : Module.Flat C (LinearMap.ker g) := Module.Flat.of_projective
  haveI : Module.Flat C (C ⊗[A] M) := Module.Flat.of_projective
  have hrk : Module.rankAtStalk (R := C) (LinearMap.ker g) = 0 := by
    funext q
    have h1 := congrFun (Module.rankAtStalk_eq_of_equiv (M := C ⊗[A] (Fin r → A))
      (N := C ⊗[A] M × LinearMap.ker g) E) q
    rw [Module.rankAtStalk_prod, Pi.add_apply, hrank q,
      Module.rankAtStalk_eq_of_equiv (piScalarRight A C C (Fin r)), Module.rankAtStalk_eq_finrank_of_free,
      Module.finrank_fin_fun] at h1
    simp only [Pi.natCast_apply, Nat.cast_id] at h1
    simp only [Pi.zero_apply]
    omega
  have hsub : Subsingleton (LinearMap.ker g) := Module.rankAtStalk_eq_zero_iff_subsingleton.mp hrk
  have hmem : (1 : C) ⊗ₜ[A] k ∈ LinearMap.ker g := by
    rw [LinearMap.mem_ker, hg, LinearMap.baseChange_tmul, hk, tmul_zero]
  have h0 : (1 : C) ⊗ₜ[A] k = 0 :=
    congrArg (fun x : LinearMap.ker g => (x : C ⊗[A] (Fin r → A))) (Subsingleton.elim (⟨_, hmem⟩ : LinearMap.ker g) 0)
  have h1 : (fun j => algebraMap A C (k j) * 1) = 0 := by
    rw [← piScalarRight_tmul, h0, map_zero]
  have := congrFun h1 i
  simpa using this

end Core

section Chart

noncomputable def pres (A : Type) [CommRing A] {M : Type} [AddCommGroup M] [Module A M] {r : ℕ}
    (A' : Type) [CommRing A'] [Algebra A A'] (m : Fin r → M) : (Fin r → A') →ₗ[A'] A' ⊗[A] M :=
  Fintype.linearCombination A' fun i => (1 : A') ⊗ₜ[A] m i

noncomputable def chartIdeal (A : Type) [CommRing A] {M : Type} [AddCommGroup M] [Module A M] {r : ℕ}
    (A' : Type) [CommRing A'] [Algebra A A'] (m : Fin r → M) : Ideal A' :=
  syz (pres A A' m)

def IsChart (A : Type) [CommRing A] {M : Type} [AddCommGroup M] [Module A M] {r : ℕ}
    (A' : Type) [CommRing A'] [Algebra A A'] (m : Fin r → M) : Prop :=
  Submodule.span A' (Set.range fun i => (1 : A') ⊗ₜ[A] m i) = ⊤

variable {A : Type} [CommRing A] {M : Type} [AddCommGroup M] [Module A M] {r : ℕ}

theorem pres_surjective {A' : Type} [CommRing A'] [Algebra A A'] {m : Fin r → M} (hm : IsChart A A' m) :
    Function.Surjective (pres A A' m) := by
  rw [← LinearMap.range_eq_top, pres, Fintype.range_linearCombination]
  exact hm

theorem chart_equiv {A' : Type} [CommRing A'] [Algebra A A'] {m : Fin r → M}
    (C : Type) [CommRing C] [Algebra A C] [Algebra A' C] [IsScalarTower A A' C]
    (hm : IsChart A A' m) (h : ∀ a ∈ chartIdeal A A' m, algebraMap A' C a = 0) :
    Nonempty ((C ⊗[A] M) ≃ₗ[C] (Fin r → C)) := by
  obtain ⟨e, -⟩ := core_equiv C (pres A A' m) (pres_surjective hm) h
  exact ⟨(AlgebraTensorModule.cancelBaseChange A A' C C M).symm ≪≫ₗ e⟩

theorem chart_vanish {A' : Type} [CommRing A'] [Algebra A A'] {m : Fin r → M}
    (C : Type) [CommRing C] [Algebra A C] [Algebra A' C] [IsScalarTower A A' C]
    (hm : IsChart A A' m) [Module.Projective C (C ⊗[A] M)]
    (hrank : ∀ q : PrimeSpectrum C, Module.rankAtStalk (C ⊗[A] M) q = r) :
    ∀ a ∈ chartIdeal A A' m, algebraMap A' C a = 0 := by
  let e := AlgebraTensorModule.cancelBaseChange A A' C C M
  haveI : Module.Projective C (C ⊗[A'] (A' ⊗[A] M)) := Module.Projective.of_equiv e.symm
  have hrank' : ∀ q : PrimeSpectrum C, Module.rankAtStalk (C ⊗[A'] (A' ⊗[A] M)) q = r := fun q => by
    rw [Module.rankAtStalk_eq_of_equiv e]; exact hrank q
  exact core_vanish C (pres A A' m) (pres_surjective hm) hrank'

end Chart

section LocalGen

variable (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] (r : ℕ)

omit [Module.Finite A M] in

theorem span_one_tmul_eq_top (L : Type) [CommRing L] [Algebra A L] :
    Submodule.span L (Set.range fun x : M => (1 : L) ⊗ₜ[A] x) = ⊤ := by
  have h := Submodule.baseChange_top (R := A) (M := M) L
  rw [Submodule.baseChange_eq_span, Submodule.map_top, LinearMap.coe_range] at h
  exact h

theorem exists_chart (p : PrimeSpectrum A)
    (hr : Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] M) ≤ r) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∃ m : Fin r → M, IsChart A (Localization.Away f) m := by
  classical
  let κ := p.asIdeal.ResidueField

  let S : Set (κ ⊗[A] M) := Set.range fun x : M => (1 : κ) ⊗ₜ[A] x
  have hS : Submodule.span κ S = ⊤ := span_one_tmul_eq_top A M κ
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent κ S
  rw [hS] at hbspan
  have hbfin : b.Finite := hbli.set_finite_of_isNoetherian
  obtain ⟨n, ι, hι⟩ := hbfin.fin_embedding
  haveI : Fintype b := hbfin.fintype
  have hn : n ≤ r := by
    have h1 : Fintype.card b ≤ Module.finrank κ (κ ⊗[A] M) := hbli.fintype_card_le_finrank
    have h2 : Fintype.card (Fin n) = Fintype.card b := by
      refine Fintype.card_congr (Equiv.ofBijective (fun i => ⟨ι i, hι ▸ Set.mem_range_self i⟩) ⟨?_, ?_⟩)
      · intro i j hij
        exact ι.injective (congrArg Subtype.val hij)
      · rintro ⟨y, hy⟩
        rw [← hι] at hy
        obtain ⟨i, rfl⟩ := hy
        exact ⟨i, rfl⟩
    rw [Fintype.card_fin] at h2
    have hr' : Module.finrank κ (κ ⊗[A] M) ≤ r := hr
    omega
  have hιS : ∀ i : Fin n, ∃ x : M, (1 : κ) ⊗ₜ[A] x = ι i := fun i => by
    have : ι i ∈ b := hι ▸ Set.mem_range_self i
    exact hbS this
  choose x hx using hιS
  let m : Fin r → M := fun i => if h : (i : ℕ) < n then x ⟨i, h⟩ else 0
  have hxm : ∀ i : Fin n, x i ∈ Set.range m := fun i => by
    refine ⟨⟨i, lt_of_lt_of_le i.2 hn⟩, ?_⟩
    simp [m]

  let N : Submodule A M := Submodule.span A (Set.range m)
  let Q := M ⧸ N
  have hzero : (N.mkQ).baseChange κ = 0 := by
    refine LinearMap.ext_on hbspan ?_
    intro y hy
    rw [← hι] at hy
    obtain ⟨i, rfl⟩ := hy
    rw [← hx i, LinearMap.baseChange_tmul, LinearMap.zero_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span (hxm i)), tmul_zero]
  have hsub : Subsingleton (κ ⊗[A] Q) := by
    refine ⟨fun y z => ?_⟩
    have hsurj : Function.Surjective ((N.mkQ).baseChange κ) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact LinearMap.lTensor_surjective κ (Submodule.mkQ_surjective N)
    obtain ⟨y', rfl⟩ := hsurj y
    obtain ⟨z', rfl⟩ := hsurj z
    rw [hzero, LinearMap.zero_apply, LinearMap.zero_apply]
  have hp : p ∉ Module.support A Q := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact hsub
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hp
  obtain ⟨f, hfann, hfp⟩ := hp
  refine ⟨f, hfp, m, ?_⟩

  let L := Localization.Away f
  let T : Submodule L (L ⊗[A] M) := Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[A] m i)
  have hT : ∀ y : M, (1 : L) ⊗ₜ[A] y ∈ T := fun y => by
    have hfy : f • y ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero N, Submodule.Quotient.mk_smul]
      exact Module.mem_annihilator.mp hfann _
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hfy
    have hmem : (1 : L) ⊗ₜ[A] (f • y) ∈ T := by
      rw [← hc, tmul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [tmul_smul, ← algebraMap_smul L (c i)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    have hunit : IsUnit (algebraMap A L f) := IsLocalization.Away.algebraMap_isUnit f
    obtain ⟨l, hl⟩ := hunit.exists_left_inv
    have h1 : (1 : L) ⊗ₜ[A] y = l • (algebraMap A L f • ((1 : L) ⊗ₜ[A] y)) := by
      rw [← mul_smul, hl, one_smul]
    rw [h1]
    refine Submodule.smul_mem _ _ ?_
    rw [algebraMap_smul, ← tmul_smul]
    exact hmem
  change T = ⊤
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul c y =>
    have : c ⊗ₜ[A] y = c • ((1 : L) ⊗ₜ[A] y) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (hT y)
  | add y z hy hz => exact Submodule.add_mem _ hy hz

end LocalGen

section Compat

variable {A : Type} [CommRing A] {M : Type} [AddCommGroup M] [Module A M] {r : ℕ}

theorem compat (g g' : A) (m m' : Fin r → M) (hm : IsChart A (Localization.Away g) m)
    (hm' : IsChart A (Localization.Away g') m') (a : A)
    (ha : algebraMap A (Localization.Away g) a ∈ chartIdeal A (Localization.Away g) m) :
    ∃ N : ℕ, algebraMap A (Localization.Away g') (a * g ^ N) ∈ chartIdeal A (Localization.Away g') m' := by
  classical
  let A' := Localization.Away g'
  let I' : Ideal A' := chartIdeal A A' m'
  let Q := A' ⧸ I'
  let gbar : Q := Ideal.Quotient.mk I' (algebraMap A A' g)
  let C := Localization.Away gbar

  have hI' : ∀ x ∈ I', algebraMap A' C x = 0 := fun x hx => by
    rw [IsScalarTower.algebraMap_apply A' Q C, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  obtain ⟨e⟩ := chart_equiv C hm' hI'
  haveI : Module.Projective C (C ⊗[A] M) := Module.Projective.of_equiv e.symm
  have hrank : ∀ q : PrimeSpectrum C, Module.rankAtStalk (C ⊗[A] M) q = r := fun q => by
    haveI := nontrivial_of_primeSpectrum q
    rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_eq_finrank_of_free, Module.finrank_fin_fun]
    rfl

  have hgC : algebraMap A C g = algebraMap Q C gbar := by
    rw [IsScalarTower.algebraMap_apply A A' C, IsScalarTower.algebraMap_apply A' Q C, Ideal.Quotient.algebraMap_eq]
  have hunit : IsUnit (algebraMap A C g) := by
    rw [hgC]; exact IsLocalization.Away.algebraMap_isUnit gbar
  letI : Algebra (Localization.Away g) C := (IsLocalization.Away.lift g hunit).toAlgebra
  haveI : IsScalarTower A (Localization.Away g) C :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq g hunit x).symm
  have hvan := chart_vanish C hm hrank _ ha
  rw [← IsScalarTower.algebraMap_apply A (Localization.Away g) C, IsScalarTower.algebraMap_apply A A' C,
    IsScalarTower.algebraMap_apply A' Q C, IsLocalization.map_eq_zero_iff (Submonoid.powers gbar) C] at hvan
  obtain ⟨⟨s, N, hs⟩, hN⟩ := hvan
  refine ⟨N, ?_⟩
  change algebraMap A A' (a * g ^ N) ∈ I'
  have hgQ : algebraMap A Q g = gbar := by
    rw [IsScalarTower.algebraMap_apply A A' Q, Ideal.Quotient.algebraMap_eq]
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply A A' Q,
    map_mul, map_pow, hgQ, IsScalarTower.algebraMap_apply A A' Q a, mul_comm]
  have hs' : gbar ^ N = s := hs
  rw [hs']
  exact hN

end Compat

section Glue

variable (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] (r : ℕ)

theorem main
    (hr : ∀ p : PrimeSpectrum A,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] M) ≤ r) :
    ∃ 𝔞 : Ideal A, ∀ (B : Type) [CommRing B] [Algebra A B],
      (Module.Projective B (B ⊗[A] M) ∧ ∀ q : PrimeSpectrum B, Module.rankAtStalk (B ⊗[A] M) q = r) ↔
        ∀ a ∈ 𝔞, algebraMap A B a = 0 := by
  classical

  choose f hf m hm using fun p : PrimeSpectrum A => exists_chart A M r p (hr p)
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    by_contra h
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ h
    exact hf ⟨𝔪, h𝔪.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨s, hs, hstop⟩ := (Ideal.span_eq_top_iff_finite _).mp hspan
  have hcov : ∀ g ∈ (s : Set A), ∃ mg : Fin r → M, IsChart A (Localization.Away g) mg := fun g hg => by
    obtain ⟨p, rfl⟩ := hs hg
    exact ⟨m p, hm p⟩
  choose! mg hmg using hcov

  let 𝔞g : ∀ g : A, Ideal (Localization.Away g) := fun g => chartIdeal A (Localization.Away g) (mg g)
  let 𝔞 : Ideal A := ⨅ g ∈ s, (𝔞g g).comap (algebraMap A (Localization.Away g))
  have mem𝔞 : ∀ a : A, a ∈ 𝔞 ↔ ∀ g ∈ s, algebraMap A (Localization.Away g) a ∈ 𝔞g g := fun a => by
    simp only [𝔞, Submodule.mem_iInf, Ideal.mem_comap]
  refine ⟨𝔞, fun B _ _ => ?_⟩

  have hchart : ∀ J : Ideal B, J ≠ ⊤ → ∃ g ∈ s, algebraMap A B g ∉ J := fun J hJ => by
    by_contra! h
    apply hJ
    rw [eq_top_iff, ← Ideal.map_top (algebraMap A B), ← hstop, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact h g hg

  have hfree : (∀ a ∈ 𝔞, algebraMap A B a = 0) → ∀ (C : Type) [CommRing C] [Algebra A C] [Algebra B C]
      [IsScalarTower A B C], ∀ g ∈ s, IsUnit (algebraMap A C g) → Nonempty ((C ⊗[A] M) ≃ₗ[C] (Fin r → C)) := by
    intro hvan C _ _ _ _ g hg hunit
    letI : Algebra (Localization.Away g) C := (IsLocalization.Away.lift g hunit).toAlgebra
    haveI : IsScalarTower A (Localization.Away g) C :=
      IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq g hunit x).symm
    refine chart_equiv C (hmg g hg) fun x hx => ?_
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) x
    obtain ⟨t, k, rfl⟩ := t
    have hspec := IsLocalization.mk'_spec (Localization.Away g) a (⟨g ^ k, k, rfl⟩ : Submonoid.powers g)
    have ha : algebraMap A (Localization.Away g) a ∈ 𝔞g g := by
      rw [← hspec]; exact Ideal.mul_mem_right _ _ hx

    have hN : ∀ g' ∈ (s : Set A), ∃ N : ℕ, ∀ n, N ≤ n →
        algebraMap A (Localization.Away g') (a * g ^ n) ∈ 𝔞g g' := fun g' hg' => by
      obtain ⟨N, hN⟩ := compat g g' (mg g) (mg g') (hmg g hg) (hmg g' hg') a ha
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, ← mul_assoc, map_mul]
      exact Ideal.mul_mem_right _ _ hN
    choose! N hN using hN
    have hmem : a * g ^ (s.sup N) ∈ 𝔞 := by
      rw [mem𝔞]
      intro g' hg'
      exact hN g' hg' _ (Finset.le_sup hg')
    have h0 : algebraMap A C a = 0 := by
      have := congrArg (algebraMap B C) (hvan _ hmem)
      rw [← IsScalarTower.algebraMap_apply, map_zero, map_mul, map_pow] at this
      exact (IsUnit.mul_left_eq_zero (hunit.pow _)).mp this
    have hspecC := congrArg (algebraMap (Localization.Away g) C) hspec
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, h0, map_pow] at hspecC
    exact (IsUnit.mul_left_eq_zero (hunit.pow _)).mp hspecC
  constructor
  ·
    rintro ⟨hproj, hrank⟩ a ha
    haveI := hproj
    haveI : Module.Finite B (B ⊗[A] M) := Module.Finite.base_change A B M
    apply eq_zero_of_localization
    intro J hJ
    obtain ⟨g, hg, hgJ⟩ := hchart J hJ.ne_top
    let C := Localization.AtPrime J
    have hunit : IsUnit (algebraMap A C g) := by
      rw [IsScalarTower.algebraMap_apply A B C]
      exact IsLocalization.map_units C (⟨algebraMap A B g, hgJ⟩ : J.primeCompl)
    letI : Algebra (Localization.Away g) C := (IsLocalization.Away.lift g hunit).toAlgebra
    haveI : IsScalarTower A (Localization.Away g) C :=
      IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq g hunit x).symm
    let e : C ⊗[B] (B ⊗[A] M) ≃ₗ[C] C ⊗[A] M := AlgebraTensorModule.cancelBaseChange A B C C M
    haveI : Module.Projective C (C ⊗[A] M) := Module.Projective.of_equiv e
    have hrankC : ∀ q : PrimeSpectrum C, Module.rankAtStalk (C ⊗[A] M) q = r := fun q => by
      rw [← Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_baseChange, hrank]
    have := chart_vanish C (hmg g hg) hrankC _ ((mem𝔞 a).mp ha g hg)
    rwa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B C] at this
  ·
    intro hvan
    have hfree := hfree hvan
    let Nmod := B ⊗[A] M

    have hstopB : Ideal.span ((algebraMap A B) '' (s : Set A)) = ⊤ := by
      rw [← Ideal.map_span, hstop, Ideal.map_top]
    haveI : Module.FinitePresentation B Nmod := by
      refine Module.FinitePresentation.of_localizationSpan _ hstopB ?_
      rintro ⟨_, g, hg, rfl⟩
      let C := Localization.Away (algebraMap A B g)
      have hunit : IsUnit (algebraMap A C g) := by
        rw [IsScalarTower.algebraMap_apply A B C]
        exact IsLocalization.Away.algebraMap_isUnit _
      obtain ⟨e⟩ := hfree C g hg hunit
      let e' : LocalizedModule.Away (algebraMap A B g) Nmod ≃ₗ[C] (Fin r → C) :=
        LocalizedModule.equivTensorProduct (Submonoid.powers (algebraMap A B g)) Nmod ≪≫ₗ
          AlgebraTensorModule.cancelBaseChange A B C C M ≪≫ₗ e
      exact Module.FinitePresentation.of_equiv e'.symm
    refine ⟨?_, fun q => ?_⟩
    · refine Module.projective_of_localization_maximal fun J hJ => ?_
      obtain ⟨g, hg, hgJ⟩ := hchart J hJ.ne_top
      let C := Localization.AtPrime J
      have hunit : IsUnit (algebraMap A C g) := by
        rw [IsScalarTower.algebraMap_apply A B C]
        exact IsLocalization.map_units C (⟨algebraMap A B g, hgJ⟩ : J.primeCompl)
      obtain ⟨e⟩ := hfree C g hg hunit
      let e' : LocalizedModule J.primeCompl Nmod ≃ₗ[C] (Fin r → C) :=
        LocalizedModule.equivTensorProduct J.primeCompl Nmod ≪≫ₗ
          AlgebraTensorModule.cancelBaseChange A B C C M ≪≫ₗ e
      exact Module.Projective.of_equiv e'.symm
    · rw [Module.rankAtStalk_eq_finrank_tensorProduct]
      obtain ⟨g, hg, hgJ⟩ := hchart q.asIdeal q.2.ne_top
      let C := Localization.AtPrime q.asIdeal
      have hunit : IsUnit (algebraMap A C g) := by
        rw [IsScalarTower.algebraMap_apply A B C]
        exact IsLocalization.map_units C (⟨algebraMap A B g, hgJ⟩ : q.asIdeal.primeCompl)
      obtain ⟨e⟩ := hfree C g hg hunit
      rw [(AlgebraTensorModule.cancelBaseChange A B C C M ≪≫ₗ e).finrank_eq, Module.finrank_fin_fun]

end Glue

end FittingClosed

theorem solution
    (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] (r : ℕ)
    (hr : ∀ p : PrimeSpectrum A,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] M) ≤ r) :
    ∃ 𝔞 : Ideal A, ∀ (B : Type) [CommRing B] [Algebra A B],
      (Module.Projective B (B ⊗[A] M) ∧ ∀ q : PrimeSpectrum B, Module.rankAtStalk (B ⊗[A] M) q = r) ↔
        ∀ a ∈ 𝔞, algebraMap A B a = 0 :=
  FittingClosed.main A M r hr

end S_Module_exists_ideal_forall_projective_and_rankAtStalk_eq_iff
end P2MW
export P2MW.S_Module_exists_ideal_forall_projective_and_rankAtStalk_eq_iff (solution)
