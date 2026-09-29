-- Prove2me | solution 1 for MvFormalGroup.exists_forall_existsUnique_eq_sum_subst_nthSeries_mul_of_finrank_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a8add937-a67c-5f20-9dca-338e840091c8

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_Module_Finite_of_isAdicComplete_of_isHausdorff_of_quotient
import Theorems.Thm_Module_Flat_of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal
import Theorems.Thm_IsRegularLocalRing_mvPowerSeries_fin
import Theorems.Thm_MvFormalGroup_finrank_quotient_span_nthSeries_pow_eq_pow
import Theorems.Thm_MvFormalGroup_finite_free_finrank_quotient_span_nthSeries_of_finrank_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_forall_existsUnique_eq_sum_subst_nthSeries_mul_of_finrank_eq_pow

set_option autoImplicit false

open MvPowerSeries

universe u v

namespace SubstFreeO

open MvPowerSeries IsLocalRing

variable {d : ℕ}

private theorem mem_span_X_pow {σ : Type*} {R : Type*} [CommRing R] [DecidableEq σ] (N : ℕ) (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ e : σ →₀ ℕ, (∀ s ∈ T, e s < N) → coeff e f = 0) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    have : f = 0 := by
      ext e
      rw [coeff_zero]
      exact hf e (fun s hs => absurd hs (Finset.notMem_empty s))
    rw [this]
    exact zero_mem _
  | insert s₀ T hs₀ ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun e => if e s₀ < N then coeff e f else 0
    have hf₀ : ∀ e, coeff e f₀ = if e s₀ < N then coeff e f else 0 := fun e => rfl
    have h1 : (X s₀ : MvPowerSeries σ R) ^ N ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hf₀, if_pos hm, sub_self]
    have h2 : f₀ ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) := by
      refine ih f₀ fun e he => ?_
      rw [hf₀]
      by_cases h : e s₀ < N
      · rw [if_pos h]
        refine hf e fun s hs => ?_
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact h
        · exact he s hs
      · rw [if_neg h]
    have h3 : Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) ≤
        Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' ((insert s₀ T : Finset σ) : Set σ)) :=
      Ideal.span_mono (Set.image_mono (by simp))
    obtain ⟨g, hg⟩ := h1
    have : f = f₀ + (X s₀ : MvPowerSeries σ R) ^ N * g := by rw [← hg]; ring
    rw [this]
    refine Ideal.add_mem _ (h3 h2) (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s₀, by simp, rfl⟩))

private theorem mem_span_range_X_of_constantCoeff {R : Type*} [CommRing R] {f : MvPowerSeries (Fin d) R}
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R)) := by
  classical
  have h := mem_span_X_pow 1 Finset.univ f fun e he => by
    have : e = 0 := by
      ext s
      have := he s (Finset.mem_univ s)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [this, coeff_zero_eq_constantCoeff_apply, hf]
  simpa only [pow_one, Finset.coe_univ, Set.image_univ] using h

private theorem constantCoeff_eq_zero_of_mem_span_range_X {R : Type*} [CommRing R] {f : MvPowerSeries (Fin d) R}
    (hf : f ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R))) : constantCoeff f = 0 := by
  have hle : Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R)) ≤
      RingHom.ker (constantCoeff : MvPowerSeries (Fin d) R →+* R) := by
    rw [Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    exact constantCoeff_X s
  exact hle hf

private theorem constantCoeff_substAlgHom {R : Type*} [CommRing R] {g : Fin d → MvPowerSeries (Fin d) R}
    (hg : ∀ i, constantCoeff (g i) = 0) (x : MvPowerSeries (Fin d) R) :
    constantCoeff (substAlgHom (hasSubst_of_constantCoeff_zero hg) x) = constantCoeff x := by
  have hx : x = algebraMap R (MvPowerSeries (Fin d) R) (constantCoeff x) + (x - C (constantCoeff x)) := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]; ring
  have h0 : constantCoeff (x - C (constantCoeff x)) = 0 := by
    rw [map_sub, constantCoeff_C, sub_self]
  conv_lhs => rw [hx]
  rw [map_add, AlgHom.commutes, map_add, coe_substAlgHom,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hg) hg h0, add_zero,
    MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_C]

private def Tgt {R : Type u} [CommRing R] {d : ℕ} (_φ : MvPowerSeries (Fin d) R →+* MvPowerSeries (Fin d) R) : Type u :=
  MvPowerSeries (Fin d) R

variable {R : Type u} [CommRing R] {d : ℕ}

private noncomputable scoped instance (φ : MvPowerSeries (Fin d) R →+* MvPowerSeries (Fin d) R) : CommRing (Tgt φ) :=
  inferInstanceAs (CommRing (MvPowerSeries (Fin d) R))

private def toTgt (φ : MvPowerSeries (Fin d) R →+* MvPowerSeries (Fin d) R) : MvPowerSeries (Fin d) R →+* Tgt φ := φ

private noncomputable scoped instance (φ : MvPowerSeries (Fin d) R →+* MvPowerSeries (Fin d) R) :
    Algebra (MvPowerSeries (Fin d) R) (Tgt φ) := (toTgt φ).toAlgebra

private theorem algebraMap_Tgt (φ : MvPowerSeries (Fin d) R →+* MvPowerSeries (Fin d) R)
    (x : MvPowerSeries (Fin d) R) : algebraMap (MvPowerSeries (Fin d) R) (Tgt φ) x = φ x := rfl

private noncomputable def ofT (φ : MvPowerSeries (Fin d) R →+* MvPowerSeries (Fin d) R) : Tgt φ ≃+* MvPowerSeries (Fin d) R :=
  RingEquiv.refl _

private theorem ofT_algebraMap (φ : MvPowerSeries (Fin d) R →+* MvPowerSeries (Fin d) R) (r : MvPowerSeries (Fin d) R) :
    ofT φ (algebraMap (MvPowerSeries (Fin d) R) (Tgt φ) r) = φ r := rfl

private theorem ofT_smul (φ : MvPowerSeries (Fin d) R →+* MvPowerSeries (Fin d) R) (r : MvPowerSeries (Fin d) R)
    (t : Tgt φ) : ofT φ (r • t) = φ r * ofT φ t := by
  rw [Algebra.smul_def, map_mul, ofT_algebraMap]

private theorem ofT_symm_apply (φ : MvPowerSeries (Fin d) R →+* MvPowerSeries (Fin d) R) (x : MvPowerSeries (Fin d) R) :
    ofT φ ((ofT φ).symm x) = x := rfl

private scoped instance [IsLocalRing R] (φ : MvPowerSeries (Fin d) R →+* MvPowerSeries (Fin d) R) : IsLocalRing (Tgt φ) :=
  inferInstanceAs (IsLocalRing (MvPowerSeries (Fin d) R))

private theorem isRegularLocalRing_Tgt (φ : MvPowerSeries (Fin d) R →+* MvPowerSeries (Fin d) R)
    (h : IsRegularLocalRing (MvPowerSeries (Fin d) R)) : IsRegularLocalRing (Tgt φ) := h

private scoped instance map_isComm {S : Type*} [CommRing S] (f : R →+* S) (F : MvFormalGroup d R) [F.IsComm] :
    (F.map f).IsComm := by
  refine ⟨fun i => ?_⟩
  have hswap : HasSubst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R)) fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> exact constantCoeff_X _)
  have key := congrArg (MvPowerSeries.map f) (MvFormalGroup.IsComm.comm (F := F) i)
  rw [MvPowerSeries.map_subst hswap] at key
  have hfam : (fun s => MvPowerSeries.map f (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun j => X (Sum.inl j)) s)) =
      Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) S)) fun j => X (Sum.inl j) := by
    funext s; rcases s with j | j <;> simp [MvPowerSeries.map_X]
  rw [hfam] at key
  exact key

end SubstFreeO
p2m_reactivate "P2MW.S_MvFormalGroup_exists_forall_existsUnique_eq_sum_subst_nthSeries_mul_of_finrank_eq_pow.SubstFreeO"

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm] (h : ℕ)
    (hh : Module.finrank (𝓞 ⧸ Ideal.span {(p : 𝓞)})
      (MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ⧸
        Ideal.span (Set.range ((Φ.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).nthSeries p))) =
      p ^ h)
    (v : ℕ) :
    ∃ e : Fin (p ^ (v * h)) → MvPowerSeries (Fin d) 𝓞,
      ∀ F : MvPowerSeries (Fin d) 𝓞, ∃! c : Fin (p ^ (v * h)) → MvPowerSeries (Fin d) 𝓞,
        F = ∑ j, MvPowerSeries.subst (Φ.nthSeries (p ^ v)) (c j) * e j := by
  classical

  obtain ⟨hD, hDVR, -, -⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal (𝓞 := 𝓞) p hp
  letI : Field (𝓞 ⧸ Ideal.span {(p : 𝓞)}) := Ideal.Quotient.field _
  have hrk := MvFormalGroup.finrank_quotient_span_nthSeries_pow_eq_pow p
    (Φ.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))) h hh v
  obtain ⟨hfinQ, -, hrkQ⟩ :=
    MvFormalGroup.finite_free_finrank_quotient_span_nthSeries_of_finrank_eq_pow p hp Φ h v hrk

  set g : Fin d → MvPowerSeries (Fin d) 𝓞 := Φ.nthSeries (p ^ v) with hgdef
  have hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0 := MvFormalGroup.constantCoeff_nthSeries Φ (p ^ v)
  haveI := hfinQ

  let φa : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] MvPowerSeries (Fin d) 𝓞 :=
    MvPowerSeries.substAlgHom (R := 𝓞) (MvPowerSeries.hasSubst_of_constantCoeff_zero hg)
  let φ : MvPowerSeries (Fin d) 𝓞 →+* MvPowerSeries (Fin d) 𝓞 := φa.toRingHom
  have hφ : ∀ x, φ x = MvPowerSeries.subst g x := fun x => by
    show φa x = _
    rw [MvPowerSeries.coe_substAlgHom]
  have hφX : ∀ i, φ (MvPowerSeries.X i) = g i := fun i => by
    rw [hφ, MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hg)]
  have hφC : ∀ c : 𝓞, φ (MvPowerSeries.C c) = MvPowerSeries.C c := fun c => by
    show φa (MvPowerSeries.C c) = _
    rw [MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
  have hφ0 : ∀ x, MvPowerSeries.constantCoeff (φ x) = MvPowerSeries.constantCoeff x := fun x =>
    SubstFreeO.constantCoeff_substAlgHom hg x

  let T := SubstFreeO.Tgt φ
  let e : T ≃+* MvPowerSeries (Fin d) 𝓞 := SubstFreeO.ofT φ
  have he_smul : ∀ (r : MvPowerSeries (Fin d) 𝓞) (t : T), e (r • t) = φ r * e t :=
    SubstFreeO.ofT_smul φ
  have he_symm : ∀ x, e (e.symm x) = x := SubstFreeO.ofT_symm_apply φ

  haveI hregA : IsRegularLocalRing (MvPowerSeries (Fin d) 𝓞) := IsRegularLocalRing.mvPowerSeries_fin 𝓞 d
  haveI hregT : IsRegularLocalRing T := SubstFreeO.isRegularLocalRing_Tgt φ hregA

  haveI hloc : IsLocalHom (algebraMap (MvPowerSeries (Fin d) 𝓞) T) := by
    refine ⟨fun x hx => ?_⟩
    have hx1 : IsUnit (e (algebraMap (MvPowerSeries (Fin d) 𝓞) T x)) := hx.map e
    rw [SubstFreeO.ofT_algebraMap] at hx1
    have hx' : IsUnit (MvPowerSeries.constantCoeff (φ x)) := MvPowerSeries.isUnit_iff_constantCoeff.mp hx1
    rw [hφ0] at hx'
    exact MvPowerSeries.isUnit_iff_constantCoeff.mpr hx'

  let 𝔫 : Ideal (MvPowerSeries (Fin d) 𝓞) := Ideal.span (Set.range MvPowerSeries.X)
  have hrg : (⇑φ) '' Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) 𝓞) = Set.range g := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hφX)
  have hmap : Ideal.map (algebraMap (MvPowerSeries (Fin d) 𝓞) T) 𝔫 =
      Ideal.comap e (Ideal.span (Set.range g)) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, Ideal.mem_comap, SubstFreeO.ofT_algebraMap, ← Ideal.mem_comap]
      have : 𝔫 ≤ Ideal.comap φ (Ideal.span (Set.range g)) := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_span, hrg]
      exact this hr
    · intro t ht
      rw [Ideal.mem_comap] at ht
      have hsurj : ∀ y ∈ Ideal.span (Set.range g), e.symm y ∈ Ideal.map (algebraMap (MvPowerSeries (Fin d) 𝓞) T) 𝔫 := by
        intro y hy
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨i, rfl⟩
          rw [← hφX]
          exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
        · rw [map_zero]; exact Ideal.zero_mem _
        · intro a b _ _ ha hb; rw [map_add]; exact Ideal.add_mem _ ha hb
        · intro a b _ hb; rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hb
      have := hsurj (e t) ht
      rwa [RingEquiv.symm_apply_apply] at this
  have hsmul : ∀ (n : ℕ) (t : T),
      t ∈ (𝔫 ^ n • ⊤ : Submodule (MvPowerSeries (Fin d) 𝓞) T) ↔
        e t ∈ (Ideal.span (Set.range g) : Ideal (MvPowerSeries (Fin d) 𝓞)) ^ n := by
    intro n t
    rw [Ideal.smul_top_eq_map, Ideal.map_pow, hmap, Submodule.restrictScalars_mem, ← Ideal.map_symm,
      ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]
  have hgne : (Ideal.span (Set.range g) : Ideal (MvPowerSeries (Fin d) 𝓞)) ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPowerSeries (Fin d) 𝓞) ∈ Ideal.span (Set.range g) := htop ▸ Submodule.mem_top
    have hle : Ideal.span (Set.range g) ≤
        RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) 𝓞 →+* 𝓞) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hg i
    have := hle h1
    rw [RingHom.mem_ker, map_one] at this
    exact one_ne_zero this

  haveI hhaus : IsHausdorff 𝔫 T := by
    refine ⟨fun z hz => ?_⟩
    have hz' : ∀ n : ℕ, e z ∈ (Ideal.span (Set.range g) : Ideal _) ^ n := fun n => by
      have h := hz n
      rw [SModEq.sub_mem, sub_zero] at h
      exact (hsmul n z).mp h
    have hmem : e z ∈ ⨅ n : ℕ, (Ideal.span (Set.range g) : Ideal _) ^ n := Ideal.mem_iInf.mpr hz'
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hgne, Ideal.mem_bot] at hmem
    exact e.map_eq_zero_iff.mp hmem

  haveI hfinq : Module.Finite (MvPowerSeries (Fin d) 𝓞) (T ⧸ (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) 𝓞) T)) := by
    obtain ⟨m, f, hf⟩ :=
      Module.Finite.exists_fin (R := 𝓞) (M := MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range g))
    choose t ht using fun j => Ideal.Quotient.mk_surjective (I := Ideal.span (Set.range g)) (f j)
    rw [Module.finite_def]
    refine ⟨(Finset.univ : Finset (Fin m)).image fun j =>
      Submodule.Quotient.mk (p := (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) 𝓞) T)) (e.symm (t j)),
        eq_top_iff.mpr ?_⟩
    rintro y -
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hx : Ideal.Quotient.mk (Ideal.span (Set.range g)) (e x) ∈ Submodule.span 𝓞 (Set.range f) := by
      rw [hf]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝓞).mp hx
    have hdiff : e x - ∑ j, c j • t j ∈ Ideal.span (Set.range g) := by
      rw [← Ideal.Quotient.eq, map_sum, ← hc]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← ht j]
      simp only [← Ideal.Quotient.mkₐ_eq_mk 𝓞, map_smul]
    have hdiff' : x - ∑ j, (MvPowerSeries.C (c j) : MvPowerSeries (Fin d) 𝓞) • e.symm (t j) ∈
        (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) 𝓞) T) := by
      rw [show (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) 𝓞) T) = 𝔫 ^ 1 • ⊤ by rw [pow_one], hsmul 1, pow_one,
        map_sub, map_sum]
      convert hdiff using 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [he_smul, he_symm, hφC, MvPowerSeries.smul_eq_C_mul]
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have hquot : Submodule.Quotient.mk (p := (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) 𝓞) T)) x =
        ∑ j, (MvPowerSeries.C (c j) : MvPowerSeries (Fin d) 𝓞) •
          Submodule.Quotient.mk (p := (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) 𝓞) T)) (e.symm (t j)) := by
      have h0 : (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) 𝓞) T).mkQ
          (x - ∑ j, (MvPowerSeries.C (c j) : MvPowerSeries (Fin d) 𝓞) • e.symm (t j)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hdiff'
      rw [map_sub, map_sum] at h0
      simp only [map_smul, Submodule.mkQ_apply] at h0
      exact sub_eq_zero.mp h0
    rw [hquot]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  haveI hfinT : Module.Finite (MvPowerSeries (Fin d) 𝓞) T :=
    Module.Finite.of_isAdicComplete_of_isHausdorff_of_quotient 𝔫 T hfinq

  haveI hflat : Module.Flat (MvPowerSeries (Fin d) 𝓞) T :=
    Module.Flat.of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq
      (MvPowerSeries (Fin d) 𝓞) T rfl
  haveI hfree : Module.Free (MvPowerSeries (Fin d) 𝓞) T := Module.free_of_flat_of_isLocalRing

  let ι := Module.Free.ChooseBasisIndex (MvPowerSeries (Fin d) 𝓞) T
  let b : Module.Basis ι (MvPowerSeries (Fin d) 𝓞) T := Module.Free.chooseBasis _ _
  have huniqT : ∀ a a' : ι → MvPowerSeries (Fin d) 𝓞, ∑ i, a i • b i = ∑ i, a' i • b i → a = a' := by
    intro a a' h
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have h0 : ∑ i, (a i - a' i) • b i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
    funext i
    exact sub_eq_zero.mp (hli _ h0 i)
  have hexp : ∀ x : MvPowerSeries (Fin d) 𝓞, x = ∑ i, φ (b.repr (e.symm x) i) * e (b i) := by
    intro x
    conv_lhs => rw [← he_symm x, ← b.sum_repr (e.symm x)]
    rw [map_sum]
    simp only [he_smul]
  have huniq : ∀ a a' : ι → MvPowerSeries (Fin d) 𝓞,
      ∑ i, φ (a i) * e (b i) = ∑ i, φ (a' i) * e (b i) → a = a' := by
    intro a a' h
    refine huniqT a a' (e.injective ?_)
    rw [map_sum, map_sum]
    simp only [he_smul]
    exact h

  let πg := Ideal.Quotient.mk (Ideal.span (Set.range g))
  have hπC : ∀ c : 𝓞, πg (MvPowerSeries.C c) = algebraMap 𝓞 _ c := fun c => by
    rw [IsScalarTower.algebraMap_apply 𝓞 (MvPowerSeries (Fin d) 𝓞) (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range g)),
      Ideal.Quotient.algebraMap_eq, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hφmod : ∀ r, πg (φ r) = algebraMap 𝓞 _ (MvPowerSeries.constantCoeff r) := by
    intro r
    have hr : r - MvPowerSeries.C (MvPowerSeries.constantCoeff r) ∈ 𝔫 :=
      SubstFreeO.mem_span_range_X_of_constantCoeff
        (by rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self])
    have h1 : φ r - MvPowerSeries.C (MvPowerSeries.constantCoeff r) ∈ Ideal.span (Set.range g) := by
      rw [← hφC, ← map_sub]
      have h2 := Ideal.mem_map_of_mem φ hr
      rwa [Ideal.map_span, hrg] at h2
    rw [← hπC, eq_comm, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    rw [← Ideal.neg_mem_iff, neg_sub]
    exact h1
  let ev : ι → MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range g) := fun i => πg (e (b i))
  have hspan : ⊤ ≤ Submodule.span 𝓞 (Set.range ev) := by
    rintro y -
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hexp x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_mul, hφmod, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent 𝓞 ev := by
    rw [Fintype.linearIndependent_iff]
    intro l hl i
    have hz : ∑ i, MvPowerSeries.C (l i) * e (b i) ∈ Ideal.span (Set.range g) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hl]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hπC, ← Algebra.smul_def]
    have hw : ∑ i, (MvPowerSeries.C (l i) : MvPowerSeries (Fin d) 𝓞) • b i ∈
        (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) 𝓞) T) := by
      rw [show (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) 𝓞) T) = 𝔫 ^ 1 • ⊤ by rw [pow_one], hsmul 1, pow_one,
        map_sum]
      simp only [he_smul, hφC]
      exact hz
    rw [← b.span_eq, Submodule.mem_ideal_smul_span_iff_exists_sum] at hw
    obtain ⟨a, ha, hsum⟩ := hw
    rw [Finsupp.sum_fintype a (fun i c => c • b i) (fun i => zero_smul (MvPowerSeries (Fin d) 𝓞) (b i))] at hsum
    have heq : (⇑a) = fun i => MvPowerSeries.C (l i) := huniqT _ _ hsum
    have hai : MvPowerSeries.C (l i) ∈ 𝔫 := by
      rw [← congrFun heq i]
      exact ha i
    have := SubstFreeO.constantCoeff_eq_zero_of_mem_span_range_X hai
    rwa [MvPowerSeries.constantCoeff_C] at this
  have hcard : Module.finrank 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range g)) = Fintype.card ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)

  have hcard' : Fintype.card ι = p ^ (v * h) := hcard.symm.trans hrkQ
  let σe : ι ≃ Fin (p ^ (v * h)) := Fintype.equivFinOfCardEq hcard'
  refine ⟨fun j => e (b (σe.symm j)), fun x => ⟨fun j => b.repr (e.symm x) (σe.symm j), ?_, ?_⟩⟩
  ·
    show x = ∑ j, MvPowerSeries.subst g (b.repr (e.symm x) (σe.symm j)) * e (b (σe.symm j))
    simp only [← hφ]
    rw [Equiv.sum_comp σe.symm (fun i => φ (b.repr (e.symm x) i) * e (b i))]
    exact hexp x
  ·
    intro c' hc'
    simp only [← hφ] at hc'
    have h1 : ∑ i, φ (c' (σe i)) * e (b i) = ∑ i, φ (b.repr (e.symm x) i) * e (b i) := by
      rw [← hexp x, hc', ← Equiv.sum_comp σe.symm (fun i => φ (c' (σe i)) * e (b i))]
      simp only [Equiv.apply_symm_apply]
    have h2 := huniq _ _ h1
    funext j
    have := congrFun h2 (σe.symm j)
    simpa only [Equiv.apply_symm_apply] using this

end S_MvFormalGroup_exists_forall_existsUnique_eq_sum_subst_nthSeries_mul_of_finrank_eq_pow
end P2MW
export P2MW.S_MvFormalGroup_exists_forall_existsUnique_eq_sum_subst_nthSeries_mul_of_finrank_eq_pow (solution)
