-- Prove2me | solution 1 for MazurP23.not_hasGaloisStableCofixedLine_of_localData
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:10:28.06926+00:00
-- url     : https://prove2.me/submissions/2b4078dd-70e1-40a6-a3d4-3d63945c28c5

import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ExtCitation_AdmissibleExtension
import Definitions.Def_ExtCitation_AdmissibleExtension_v2
import Definitions.Def_WeierstrassCurve_TorsionIntegral
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow
import Theorems.Thm_WeierstrassCurve_smul_eq_det_smul_of_cofixed
import Theorems.Thm_WeierstrassCurve_valuation_pow_eq_of_torsion_odd_of_not_inZeroComponentAt
import Theorems.Thm_AddSubgroup_inZeroComponentAt_of_cyclic_stable_scalar_dichotomy
import Theorems.Thm_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_exists_atP_filtration_of_goodReduction
import Theorems.Thm_AddSubgroup_eq_atP_filtration_of_cyclic_stable_inertia_nontrivial
import Theorems.Thm_AddSubgroup_exists_towerStep_of_extVanishingCts
import Theorems.Thm_AddSubgroup_galois_trivial_quotient_of_inertia_absorbing
import Theorems.Thm_WeierstrassCurve_isOpen_torsionBy_fixingSubgroup
import Theorems.Thm_WeierstrassCurve_frobenius_cayleyHamilton_on_torsion
import Theorems.Thm_WeierstrassCurve_Affine_Point_finite_of_finite_field
import Theorems.Thm_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow
import Theorems.Thm_ExtCitation_extVanishingCts_of_three_le
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Theorems.Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_smul
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
import Theorems.Thm_WeierstrassCurve_exists_torsion_not_inZeroComponentAt_of_ne_residueChar
import Theorems.Thm_WeierstrassCurve_exists_torsion_ne_zero_inZeroComponentAt_of_ne_residueChar
import Theorems.Thm_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one
import Theorems.Thm_ExtCitation_map_primitiveRoot_eq_pow_cycloExp
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_det_galoisRep_surjOn_inertia
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_slope_mem_of_shallow
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_level_eq_of_branch_ne
import Theorems.Thm_WeierstrassCurve_mazurStepThree_not_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_exists_quotientDatum_of_galois_stable_primeCard
import Theorems.Thm_WeierstrassCurve_exists_quotientDatum_of_galois_stable_primePowCard
import Theorems.Thm_AddSubgroup_mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub
import Theorems.Thm_WeierstrassCurve_prime_dvd_card_point_of_cofixed_addSubgroup_of_goodReduction
import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

namespace MazurP23

private theorem tw_submodule_eq_top_of_card_eq {R : Type*} [Semiring R] {V : Type*}
    [AddCommGroup V] [Module R V] [Finite V] {N : Submodule R V}
    (h : Nat.card ↥N = Nat.card V) : N = ⊤ := by
  rw [_root_.eq_top_iff]; intro x _
  have hbij := N.subtype_injective.bijective_of_nat_card_le (by rw [h])
  obtain ⟨⟨y, hy⟩, hy'⟩ := hbij.2 x
  exact hy' ▸ hy

private theorem tw_card_line {p : ℕ} (hp : p.Prime) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (hcard : Nat.card V = p ^ 2)
    {L : Submodule (ZMod p) V} (hLbot : L ≠ ⊥) (hLtop : L ≠ ⊤) : Nat.card ↥L = p := by
  have hfin : Finite V := Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero 2 hp.pos.ne')
  have hdvd : Nat.card ↥L ∣ p ^ 2 := by
    rw [← hcard, L.card_eq_card_quotient_mul_card]; exact dvd_mul_right _ _
  obtain ⟨k, hk, hkN⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases k
  · exact absurd
      (have := (Nat.card_eq_one_iff_unique.mp (by simpa using hkN)).1
       Submodule.eq_bot_of_subsingleton) hLbot
  · simpa using hkN
  · exact absurd (tw_submodule_eq_top_of_card_eq (hkN.trans hcard.symm)) hLtop

private theorem tw_addSubgroup_eq_of_le_of_card_eq {M : Type*} [AddCommGroup M]
    {H K : AddSubgroup M} (hle : H ≤ K) [Finite K]
    (hc : Nat.card ↥H = Nat.card ↥K) : H = K := by
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, SetLike.coe_sort_coe]
  exact hc.ge

private theorem tw_dich (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσD : σ ∈ A.decompositionSubgroup ℚ)
    {n : ℕ} (hn : Odd n) (hn1 : 1 < n) (hnq : ¬ q ∣ n)
    (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (htor : n • x = 0) (hout : ¬ W.InZeroComponentAt A x) :
    W.InZeroComponentAt A (σ • x - x) ∨ W.InZeroComponentAt A (σ • x + x) := by
  classical

  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, -⟩ :=
    WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction W hq hΔ hqΔ hqc₄ A hA

  rcases hP : x with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd (Or.inl hP) hout
  rw [hP] at hout htor
  have hX : A.valuation (x₁ - x₀) < 1 :=
    (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre
      W A hx₀ hy₀ hFy hFx hnode hbad h₁).mp hout

  obtain ⟨hns, hσsome⟩ : ∃ hns :
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular (σ x₁) (σ y₁),
      σ • (Point.some x₁ y₁ h₁ :
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
        = Point.some (σ x₁) (σ y₁) hns :=
    ⟨_, Point.map_some σ.toAlgHom h₁⟩

  have houtσ : ¬ W.InZeroComponentAt A (Point.some (σ x₁) (σ y₁) hns) := by
    intro hin
    refine hout ?_
    have h2 := WeierstrassCurve.inZeroComponentAt_smul W A
      (inv_mem hσD) (P := Point.some (σ x₁) (σ y₁) hns) hin
    rwa [← hσsome, inv_smul_smul] at h2
  have hXσ : A.valuation (σ x₁ - x₀) < 1 :=
    (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre
      W A hx₀ hy₀ hFy hFx hnode hbad hns).mp houtσ

  have hvmap : ∀ z : AlgebraicClosure ℚ, A.valuation (σ z) = A.valuation z := fun z =>
    ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A hσD z
  have hd0 : A.valuation (σ x₀ - x₀) < 1 := by
    have hsplit : σ x₀ - x₀ = (σ x₀ - σ x₁) + (σ x₁ - x₀) := by ring
    have h1 : A.valuation (σ x₀ - σ x₁) < 1 := by
      have : σ x₀ - σ x₁ = σ (x₀ - x₁) := (map_sub σ x₀ x₁).symm
      rw [this, hvmap, show x₀ - x₁ = -(x₁ - x₀) by ring, Valuation.map_neg]
      exact hX
    calc A.valuation (σ x₀ - x₀) ≤ max (A.valuation (σ x₀ - σ x₁)) (A.valuation (σ x₁ - x₀)) :=
          hsplit ▸ A.valuation.map_add _ _
      _ < 1 := max_lt h1 hXσ

  have hb₂ : ((W.b₂ : ℤ) : AlgebraicClosure ℚ)
      = ((W.a₁ : ℤ) : AlgebraicClosure ℚ) ^ 2 + 4 * ((W.a₂ : ℤ) : AlgebraicClosure ℚ) := by
    rw [show W.b₂ = W.a₁ ^ 2 + 4 * W.a₂ from rfl]; push_cast; ring
  have hb₄ : ((W.b₄ : ℤ) : AlgebraicClosure ℚ)
      = 2 * ((W.a₄ : ℤ) : AlgebraicClosure ℚ)
        + ((W.a₁ : ℤ) : AlgebraicClosure ℚ) * ((W.a₃ : ℤ) : AlgebraicClosure ℚ) := by
    rw [show W.b₄ = 2 * W.a₄ + W.a₁ * W.a₃ from rfl]; push_cast; ring
  have hcrit : 6 * x₀ ^ 2 + ((W.b₂ : ℤ) : AlgebraicClosure ℚ) * x₀
      + ((W.b₄ : ℤ) : AlgebraicClosure ℚ) = 0 := by
    rw [hb₂, hb₄]
    linear_combination ((W.a₁ : ℤ) : AlgebraicClosure ℚ) * hFy - 2 * hFx
  have hσcrit : 6 * (σ x₀) ^ 2 + ((W.b₂ : ℤ) : AlgebraicClosure ℚ) * (σ x₀)
      + ((W.b₄ : ℤ) : AlgebraicClosure ℚ) = 0 := by
    have h0 := congrArg σ hcrit
    simp only [map_add, map_mul, map_pow, map_ofNat, map_intCast, _root_.map_zero] at h0
    exact h0
  have hσx₀ : σ x₀ = x₀ := by
    have hfact : (x₀ - σ x₀) *
        (6 * (x₀ + σ x₀) + ((W.b₂ : ℤ) : AlgebraicClosure ℚ)) = 0 := by
      linear_combination hcrit - hσcrit
    rcases mul_eq_zero.mp hfact with h | h
    · exact (sub_eq_zero.mp h).symm
    · exfalso
      have heq : ((W.b₂ : ℤ) : AlgebraicClosure ℚ) + 12 * x₀ = 6 * (x₀ - σ x₀) := by
        linear_combination h
      have h6A : A.valuation (6 : AlgebraicClosure ℚ) ≤ 1 := by
        refine (ValuationSubring.valuation_le_one_iff A _).mpr ?_
        exact_mod_cast _root_.natCast_mem A 6
      have hlt : A.valuation (6 * (x₀ - σ x₀)) < 1 := by
        rw [Valuation.map_mul]
        calc A.valuation (6 : AlgebraicClosure ℚ) * A.valuation (x₀ - σ x₀)
            ≤ 1 * A.valuation (x₀ - σ x₀) := mul_le_mul_left h6A _
          _ = A.valuation (x₀ - σ x₀) := one_mul _
          _ < 1 := by
              rw [show x₀ - σ x₀ = -(σ x₀ - x₀) by ring, Valuation.map_neg]; exact hd0
      rw [heq] at hnode
      exact absurd hnode hlt.ne
  have hσy₀ : σ y₀ = y₀ := by
    have h0 := congrArg σ hFy
    simp only [map_add, map_mul, map_ofNat, map_intCast, _root_.map_zero] at h0
    rw [hσx₀] at h0
    have h2 : (2 : AlgebraicClosure ℚ) ≠ 0 := two_ne_zero
    exact mul_left_cancel₀ h2 (by linear_combination h0 - hFy)

  obtain ⟨hshΔ, -⟩ :=
    WeierstrassCurve.valuation_pow_eq_of_torsion_odd_of_not_inZeroComponentAt
      W hq hΔ hqΔ hqc₄ A hA hx₀ hy₀ hFy hFx hnode hbad hn hn1 hnq h₁ htor hX
  have hΔF := WeierstrassCurve.valuation_discriminant_eq_of_criticalCentre
    W A hx₀ hy₀ hFy hFx hnode hbad
  rw [hΔF] at hshΔ

  obtain ⟨hΛA, -, -⟩ :=
    WeierstrassCurve.slope_mem_of_shallow W A hx₀ hy₀ hFy hFx h₁ hX hshΔ
  have hΛσA : σ ((y₁ - y₀) / (x₁ - x₀)) ∈ A :=
    ValuationSubring.mem_of_valuation_le_one A _
      (by rw [hvmap]; exact (ValuationSubring.valuation_le_one_iff A _).mpr hΛA)
  have hσlam : σ ((y₁ - y₀) / (x₁ - x₀)) = (σ y₁ - y₀) / (σ x₁ - x₀) := by
    rw [map_div₀, map_sub, map_sub, hσx₀, hσy₀]

  have hlev : A.valuation (σ x₁ - x₀) = A.valuation (x₁ - x₀) := by
    rw [show σ x₁ - x₀ = σ (x₁ - x₀) by rw [map_sub, hσx₀], hvmap]

  have hsubA : σ ((y₁ - y₀) / (x₁ - x₀)) - (y₁ - y₀) / (x₁ - x₀) ∈ A :=
    sub_mem hΛσA hΛA
  have hsuble : A.valuation ((σ y₁ - y₀) / (σ x₁ - x₀) - (y₁ - y₀) / (x₁ - x₀)) ≤ 1 := by
    rw [← hσlam]
    exact (ValuationSubring.valuation_le_one_iff A _).mpr hsubA
  rcases lt_or_eq_of_le hsuble with hbr | hbr
  ·
    left
    have hcloser :=
      WeierstrassCurve.inZeroComponentAt_sub_of_level_eq_of_branch_eq
        W A hx₀ hy₀ hFy hFx hnode hbad hns h₁ hXσ hX hlev
        (by rw [hlev]; exact hshΔ) hbr
    rw [hσsome]
    exact hcloser.1
  ·
    right
    have hcloser :=
      WeierstrassCurve.inZeroComponentAt_add_of_level_eq_of_branch_ne
        W A hx₀ hy₀ hFy hFx hnode hbad hns h₁ hXσ hX hlev
        (by rw [hlev]; exact hshΔ) hbr
    rw [hσsome]
    exact hcloser.1

private theorem tw_mem_tor {M : Type*} [AddCommGroup M] (n : ℕ) (x : M) :
    x ∈ Submodule.torsionBy ℤ M ((n : ℕ) : ℤ) ↔ n • x = 0 := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]

private theorem tw_hM (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q)
    (hcard1 : Nat.card (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) = p ^ 2) :
    Nat.card {x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point //
      p • x = 0 ∧ W.InZeroComponentAt A x} = p := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨M, hMiff, -, -⟩ :=
    WeierstrassCurve.exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
      W hq hΔ hqΔ hqc₄ A hA (ℓ := p) hp
  have e : {x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point //
      p • x = 0 ∧ W.InZeroComponentAt A x} ≃ ↥M :=
    { toFun := fun s => ⟨⟨s.1, (tw_mem_tor p s.1).mpr s.2.1⟩, (hMiff _).mpr s.2.2⟩
      invFun := fun m => ⟨(m.1 : _), ⟨(tw_mem_tor p _).mp m.1.2, (hMiff m.1).mp m.2⟩⟩
      left_inv := fun s => rfl
      right_inv := fun m => rfl }
  rw [Nat.card_congr e]
  have hMbot : M ≠ ⊥ := by
    obtain ⟨P0, hP0ne, hP0in⟩ :=
      WeierstrassCurve.exists_torsion_ne_zero_inZeroComponentAt_of_ne_residueChar
        W hq hΔ hqΔ hqc₄ A hA (ℓ := p) hp hpq
    intro h
    refine hP0ne ?_
    have hmem := (hMiff P0).mpr hP0in
    rw [h] at hmem
    simpa using hmem
  have hMtop : M ≠ ⊤ := by
    obtain ⟨P1, hP1out⟩ :=
      WeierstrassCurve.exists_torsion_not_inZeroComponentAt_of_ne_residueChar
        W hq hΔ hqΔ hqc₄ A hA (ℓ := p) hp hpq
    exact fun h => hP1out ((hMiff P1).mp (h ▸ Submodule.mem_top))
  exact tw_card_line hp hcard1 hMbot hMtop

private theorem tw_det_seam (W : WeierstrassCurve ℤ) (p : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((DistribSMul.toAddMonoidHom (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) σ).toZModLinearMap p)
      = LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
          (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ) := by
  congr 1

private theorem tw_isElliptic (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) :
    (W.map (Int.castRingHom ℚ)).IsElliptic := by
  refine (WeierstrassCurve.isElliptic_iff _).mpr (isUnit_iff_ne_zero.mpr ?_)
  rw [WeierstrassCurve.map_Δ, eq_intCast]
  exact_mod_cast hΔ

private theorem tw_det_eq_cyclo (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)
      = ((ExtCitation.cycloExp p σ : ℕ) : ZMod p) := by
  classical
  have hp : p.Prime := Fact.out
  haveI := tw_isElliptic W hΔ
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpK : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have h1 : σ ξ = ξ ^ (LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)).val := by
    have h0 := WeierstrassCurve.apply_eq_pow_det_galoisRep_of_pow_eq_one
      (W.map (Int.castRingHom ℚ)) hp hpK σ ξ hξ.pow_eq_one
    rwa [tw_det_seam] at h0
  have h2 : σ ξ = ξ ^ ExtCitation.cycloExp p σ :=
    ExtCitation.map_primitiveRoot_eq_pow_cycloExp σ hξ
  have hord : IsOfFinOrder ξ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hξ.pow_eq_one⟩
  have h4 : (LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)).val
      ≡ ExtCitation.cycloExp p σ [MOD p] := by
    have h5 := hord.pow_eq_pow_iff_modEq.mp (h1.symm.trans h2)
    rwa [← hξ.eq_orderOf] at h5
  calc LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)
      = ((LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
          (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)).val : ZMod p) := by
        rw [ZMod.natCast_val, ZMod.cast_id]
    _ = ((ExtCitation.cycloExp p σ : ℕ) : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr h4

private theorem tw_det_frob (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : A.IsFrobeniusAt σ q) :
    LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)
      = ((q : ℕ) : ZMod p) := by
  classical
  have hp : p.Prime := Fact.out
  haveI := tw_isElliptic W hΔ
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpK : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have h1 : σ ξ = ξ ^ (LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)).val := by
    have h0 := WeierstrassCurve.apply_eq_pow_det_galoisRep_of_pow_eq_one
      (W.map (Int.castRingHom ℚ)) hp hpK σ ξ hξ.pow_eq_one
    rwa [tw_det_seam] at h0
  have h2 : σ ξ = ξ ^ q :=
    ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow hp hq hqp A hA hσ ξ hξ.pow_eq_one
  have hord : IsOfFinOrder ξ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hξ.pow_eq_one⟩
  have h4 : (LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)).val ≡ q [MOD p] := by
    have h5 := hord.pow_eq_pow_iff_modEq.mp (h1.symm.trans h2)
    rwa [← hξ.eq_orderOf] at h5
  calc LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)
      = ((LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
          (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)).val : ZMod p) := by
        rw [ZMod.natCast_val, ZMod.cast_id]
    _ = ((q : ℕ) : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h4

private theorem tw_psmul_surj {M : Type*} [AddCommGroup M] (p : ℕ) (hp : p.Prime) (s : ℕ)
    (hcS : Nat.card (Submodule.torsionBy ℤ M ((p ^ (s + 1) : ℕ) : ℤ)) = p ^ (2 * (s + 1)))
    (hcs : Nat.card (Submodule.torsionBy ℤ M ((p ^ s : ℕ) : ℤ)) = p ^ (2 * s))
    (hc1 : Nat.card (Submodule.torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) = p ^ (2 * 1))
    (e : M) (he : p • e = 0) : ∃ y : M, p ^ (s + 1) • y = 0 ∧ p ^ s • y = e := by
  classical
  set T : Submodule ℤ M := Submodule.torsionBy ℤ M ((p ^ (s + 1) : ℕ) : ℤ) with hT
  set T1 : Submodule ℤ M := Submodule.torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ) with hT1
  have hfinT : Finite ↥T :=
    Nat.finite_of_card_ne_zero (hcS ▸ pow_ne_zero _ hp.pos.ne')
  have hfinT1 : Finite ↥T1 :=
    Nat.finite_of_card_ne_zero (hc1 ▸ pow_ne_zero _ hp.pos.ne')

  have hmapmem : ∀ y : ↥T, p ^ s • (y : M) ∈ T1 := by
    intro y
    rw [hT1, tw_mem_tor]
    have hy := (tw_mem_tor (p ^ (s + 1)) (y : M)).mp y.2
    rw [pow_one, ← mul_nsmul, ← pow_succ]
    exact hy
  let f : ↥T →+ ↥T1 :=
    AddMonoidHom.mk' (fun y => ⟨p ^ s • (y : M), hmapmem y⟩)
      (fun a b => by ext; simp [smul_add])

  have hker : Nat.card f.ker = p ^ (2 * s) := by
    rw [← hcs]
    have hto : ∀ y : ↥f.ker, p ^ s • ((y.1 : M)) = 0 := by
      intro y
      have h0 : f y.1 = 0 := AddMonoidHom.mem_ker.mp y.2
      exact congrArg Subtype.val h0
    have hfrom1 : ∀ y : ↥(Submodule.torsionBy ℤ M ((p ^ s : ℕ) : ℤ)),
        (y : M) ∈ T := by
      intro y
      rw [hT, tw_mem_tor]
      have hy := (tw_mem_tor (p ^ s) (y : M)).mp y.2
      rw [pow_succ, mul_nsmul, hy, smul_zero]
    have hfrom2 : ∀ y : ↥(Submodule.torsionBy ℤ M ((p ^ s : ℕ) : ℤ)),
        (⟨(y : M), hfrom1 y⟩ : ↥T) ∈ f.ker := by
      intro y
      refine AddMonoidHom.mem_ker.mpr (Subtype.ext ?_)
      exact (tw_mem_tor (p ^ s) (y : M)).mp y.2
    exact Nat.card_congr
      { toFun := fun y => ⟨(y.1 : M), (tw_mem_tor _ _).mpr (hto y)⟩
        invFun := fun y => ⟨⟨(y : M), hfrom1 y⟩, hfrom2 y⟩
        left_inv := fun y => by ext; rfl
        right_inv := fun y => by ext; rfl }

  have hlag : Nat.card ↥T = Nat.card (↥T ⧸ f.ker) * Nat.card f.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have hquot : Nat.card (↥T ⧸ f.ker) = p ^ 2 := by
    have hks : (p : ℕ) ^ (2 * s) ≠ 0 := pow_ne_zero _ hp.pos.ne'
    have h1 : p ^ (2 * (s + 1)) = Nat.card (↥T ⧸ f.ker) * p ^ (2 * s) := by
      rw [← hker, ← hlag, hcS]
    have h2 : p ^ (2 * (s + 1)) = p ^ 2 * p ^ (2 * s) := by ring
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hks) (by rw [← h1, h2])).symm
  have hcr : Nat.card f.range = p ^ 2 := by
    rw [← hquot]
    exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv).symm
  have hrange : f.range = (⊤ : AddSubgroup ↥T1) := by
    apply tw_addSubgroup_eq_of_le_of_card_eq le_top
    rw [hcr, Nat.card_congr AddSubgroup.topEquiv.toEquiv, hc1]

  have heT1 : e ∈ T1 := by rw [hT1, tw_mem_tor, pow_one]; exact he
  have hsurj : ∃ y : ↥T, f y = ⟨e, heT1⟩ := by
    refine AddMonoidHom.mem_range.mp ?_
    rw [hrange]
    exact AddSubgroup.mem_top _
  obtain ⟨y, hy⟩ := hsurj
  exact ⟨(y : M), (tw_mem_tor (p ^ (s + 1)) _).mp y.2, Subtype.ext_iff.mp hy⟩

private theorem tw_unramified_good (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hgood : ¬ (ℓ : ℤ) ∣ W.Δ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    {n : ℕ} (hn : ¬ ℓ ∣ n)
    (y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hy : n • y = 0) :
    τ • y = y := by
  classical

  obtain ⟨τ', hτ'I, hττ'⟩ := Subgroup.mem_map.mp hτ

  have hVW : (W.map (Int.castRingHom A)).map A.subtype
      = ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)) := by
    show (W.map (Int.castRingHom A)).map A.subtype
      = (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    congr 1
  have hΔred : ((W.map (Int.castRingHom A)).map (IsLocalRing.residue A)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ]
    exact ValuationSubring.residue_intCast_ne_zero hℓ hA hgood
  have hnres : ((n : ℕ) : IsLocalRing.ResidueField A) ≠ 0 := by
    have h0 := ValuationSubring.residue_intCast_ne_zero hℓ hA
      (n := (n : ℤ)) (by exact_mod_cast hn)
    have h2 : ((n : ℤ) : A) = ((n : ℕ) : A) := by push_cast; rfl
    rw [h2, map_natCast] at h0
    exact h0

  rcases hPy : y with _ | ⟨x₁, y₁, h₁⟩
  · rfl

  obtain ⟨hns, hτsome⟩ : ∃ hns :
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular (τ x₁) (τ y₁),
      τ • (Point.some x₁ y₁ h₁ :
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
        = Point.some (τ x₁) (τ y₁) hns :=
    ⟨_, Point.map_some τ.toAlgHom h₁⟩
  rw [hPy] at hy
  have hy' : n • (Point.some (τ x₁) (τ y₁) hns :
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 := by
    have h2 : τ • (n • (Point.some x₁ y₁ h₁ :
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point))
        = n • (τ • (Point.some x₁ y₁ h₁ :
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) := by
      rw [← natCast_zsmul, WeierstrassCurve.Affine.Point.algEquiv_smul_zsmul, natCast_zsmul]
    rw [← hτsome, ← h2, hy]
    rfl

  have hτD : τ ∈ A.decompositionSubgroup ℚ := hττ' ▸ τ'.2
  have hfix := WeierstrassCurve.fixed_of_mem_inertia_of_nsmul_eq_zero
    (A := A) (W := W.map (Int.castRingHom A)) hVW hΔred (σ := τ) hτD
    (by
      have heq : (⟨τ, hτD⟩ : A.decompositionSubgroup ℚ) = τ' := Subtype.ext hττ'.symm
      rw [heq]
      exact hτ'I)
    hnres h₁ hns hy hy'
  rw [hτsome]
  simp only [hfix.1, hfix.2]

private theorem m3c_escape (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp' : p ∉ ({2, 3, 5, 7, 13} : Finset ℕ))
    (hcard1 : Nat.card (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) = p ^ 2)
    (NA : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hNAcard : Nat.card ↥NA = p)
    (e : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (he : p • e = 0) (heNA : e ∉ NA)
    (hCofe : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • e - e ∈ NA)
    (h2Δ : ((2 : ℕ) : ℤ) ∣ W.Δ) (h2c₄ : ¬ ((2 : ℕ) : ℤ) ∣ W.c₄)
    (h3Δ : ((3 : ℕ) : ℤ) ∣ W.Δ) (h3c₄ : ¬ ((3 : ℕ) : ℤ) ∣ W.c₄)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (m : ℕ) (hm : 1 ≤ m)
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hKcard : Nat.card K = p ^ m) (hK1 : IsAddCyclic ↥K)
    (hKtors : ∀ x ∈ K, p ^ m • x = 0)
    (hKstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ K, σ • x ∈ K)
    (hKdown : ∀ x ∈ K, p • x = 0 → x ∈ NA) (hNAle : NA ≤ K)
    (hanch2 : ∀ A₂ : ValuationSubring (AlgebraicClosure ℚ), A₂.LiesOverPrime 2 →
      (∀ x ∈ K, W.InZeroComponentAt A₂ x) ∧
        (∀ x, p ^ m • x = 0 → W.InZeroComponentAt A₂ x → x ∈ K))
    (hanch3 : ∀ A₃ : ValuationSubring (AlgebraicClosure ℚ), A₃.LiesOverPrime 3 →
      (∀ x ∈ K, W.InZeroComponentAt A₃ x) ∧
        (∀ x, p ^ m • x = 0 → W.InZeroComponentAt A₃ x → x ∈ K)) :
    (∀ x ∈ K, p • x = 0 → W.InZeroComponentAt A x) ∧
      (∀ x, p ^ m • x = 0 → W.InZeroComponentAt A x → x ∈ K) := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨W', φ, hΔ', hker, hφeq, hclause⟩ :=
    WeierstrassCurve.exists_quotientDatum_of_galois_stable_primePowCard W hΔ hp
      (fun V hΔV L hLcard hLstab =>
        WeierstrassCurve.exists_quotientDatum_of_galois_stable_primeCard
          V hΔV hp hp2 L hLcard hLstab)
      m K hKcard hK1 hKtors hKstab

  have heK : e ∉ K := fun hmem => heNA (hKdown e hmem he)
  have hQ0 : φ e ≠ 0 := by
    intro h0
    refine heK ?_
    have h1 : e ∈ φ.ker := AddMonoidHom.mem_ker.mpr h0
    rwa [hker] at h1
  have hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • φ e = φ e := by
    intro σ
    have h1 : σ • e - e ∈ φ.ker := by rw [hker]; exact hNAle (hCofe σ)
    have h2 : φ (σ • e) - φ e = 0 := by
      rw [← map_sub]
      exact AddMonoidHom.mem_ker.mp h1
    rw [← hφeq σ e]
    exact sub_eq_zero.mp h2
  have hQtor : p • φ e = 0 := by rw [← map_nsmul, he, _root_.map_zero]
  have hQord : addOrderOf (φ e) = p := addOrderOf_eq_prime hQtor hQ0

  have hetor : p ^ m • e = 0 := by
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [hj, pow_succ', mul_nsmul, he, nsmul_zero]

  have h2ne : (2 : ℕ) ≠ p := fun h => hp2 h.symm
  have h3ne : (3 : ℕ) ≠ p := by
    intro h
    exact hp' (by rw [← h]; decide)
  obtain ⟨h2Δ', h2c₄', htr2⟩ := hclause 2 Nat.prime_two h2ne h2Δ h2c₄
  obtain ⟨h3Δ', h3c₄', htr3⟩ := hclause 3 Nat.prime_three h3ne h3Δ h3c₄
  have hanchQ : ∀ (q₀ : ℕ),
      (∀ A₀ : ValuationSubring (AlgebraicClosure ℚ), A₀.LiesOverPrime q₀ →
        (∀ x ∈ K, W.InZeroComponentAt A₀ x) ∧
          (∀ x, p ^ m • x = 0 → W.InZeroComponentAt A₀ x → x ∈ K)) →
      (∀ A₀ : ValuationSubring (AlgebraicClosure ℚ), A₀.LiesOverPrime q₀ →
        ∀ y, (W'.InZeroComponentAt A₀ (φ y) ↔
          ∃ k ∈ K, W.InZeroComponentAt A₀ (y - k))) →
      ∀ A₀ : ValuationSubring (AlgebraicClosure ℚ), A₀.LiesOverPrime q₀ →
        ¬ W'.InZeroComponentAt A₀ (φ e) := by
    intro q₀ hanch htr A₀ hA₀ hQz
    obtain ⟨k, hk, hz⟩ := (htr A₀ hA₀ e).mp hQz
    obtain ⟨hKz, hzK⟩ := hanch A₀ hA₀
    have hnk : W.InZeroComponentAt A₀ (-k) := hKz _ (K.neg_mem hk)
    have he' : W.InZeroComponentAt A₀ e := by
      have h := WeierstrassCurve.inZeroComponentAt_sub W A₀ hz hnk
      rwa [sub_neg_eq_add, sub_add_cancel] at h
    exact heK (hzK e hetor he')
  have h2' : ∀ A₂ : ValuationSubring (AlgebraicClosure ℚ), A₂.LiesOverPrime 2 →
      ¬ W'.InZeroComponentAt A₂ (φ e) := hanchQ 2 hanch2 htr2
  have h3' : ∀ A₃ : ValuationSubring (AlgebraicClosure ℚ), A₃.LiesOverPrime 3 →
      ¬ W'.InZeroComponentAt A₃ (φ e) := hanchQ 3 hanch3 htr3

  obtain ⟨hqΔ', hqc₄', htrq⟩ := hclause q hq hqp hqΔ hqc₄
  have h2Δ'n : (2 : ℤ) ∣ W'.Δ := by exact_mod_cast h2Δ'
  have h2c₄'n : ¬ (2 : ℤ) ∣ W'.c₄ := by exact_mod_cast h2c₄'
  have h3Δ'n : (3 : ℤ) ∣ W'.Δ := by exact_mod_cast h3Δ'
  have h3c₄'n : ¬ (3 : ℤ) ∣ W'.c₄ := by exact_mod_cast h3c₄'
  have hS3 : ¬ W'.InZeroComponentAt A (φ e) :=
    WeierstrassCurve.mazurStepThree_not_inZeroComponentAt hp hp' W' hΔ' (φ e)
      hQfix hQord h2Δ'n h2c₄'n h2' h3Δ'n h3c₄'n h3' hq hqp hqΔ' hqc₄' A hA
  have hStep3 : ∀ k ∈ K, ¬ W.InZeroComponentAt A (e - k) :=
    fun k hk hz => hS3 ((htrq A hA e).mpr ⟨k, hk, hz⟩)

  have hzK : ∀ x, p ^ m • x = 0 → W.InZeroComponentAt A x → x ∈ K :=
    AddSubgroup.mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub
      W A p m K hKcard hKtors e he hcard1
      (fun x y _ _ hx hy => WeierstrassCurve.inZeroComponentAt_sub W A hx hy)
      hStep3

  refine ⟨?_, hzK⟩
  have hMcard := tw_hM W hq hΔ hqΔ hqc₄ A hA p (fun h => hqp h.symm) hcard1
  haveI : Finite ↥NA := Nat.finite_of_card_ne_zero (hNAcard ▸ hp.pos.ne')
  have hMtoNA : ∀ s : {z : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point //
      p • z = 0 ∧ W.InZeroComponentAt A z}, s.1 ∈ NA := by
    intro s
    have hstor : p ^ m • s.1 = 0 := by
      obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rw [hj, pow_succ', mul_nsmul, s.2.1, nsmul_zero]
    exact hKdown s.1 (hzK s.1 hstor s.2.2) s.2.1
  have hinj : Function.Injective (fun s : {z : ((W.map
      (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point //
      p • z = 0 ∧ W.InZeroComponentAt A z} => (⟨s.1, hMtoNA s⟩ : ↥NA)) := by
    intro a b hab
    have hv : a.1 = b.1 := congrArg (fun z : ↥NA => (z : ((W.map
        (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) hab
    exact Subtype.ext hv
  have hbij : Function.Bijective (fun s : {z : ((W.map
      (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point //
      p • z = 0 ∧ W.InZeroComponentAt A z} => (⟨s.1, hMtoNA s⟩ : ↥NA)) :=
    hinj.bijective_of_nat_card_le (by rw [hMcard, hNAcard])
  intro x hx hpx
  obtain ⟨z, hzeq⟩ := hbij.2 ⟨x, hKdown x hx hpx⟩
  have hzx : z.1 = x := congrArg Subtype.val hzeq
  exact hzx ▸ z.2.2

/-- A large prime admits no Galois-stable cofixed line under the stated local hypotheses. -/
theorem _root_.solution
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} (hp : p.Prime) (hp17 : 17 ≤ p)
    (h2Δ : (2:ℤ) ∣ W.Δ) (h2c₄ : ¬ (2:ℤ) ∣ W.c₄)
    (h3Δ : (3:ℤ) ∣ W.Δ) (h3c₄ : ¬ (3:ℤ) ∣ W.c₄)
    (hloc : ∀ q : ℕ, q.Prime → q ≠ p →
      ¬ (q : ℤ) ∣ W.Δ ∨ ((q : ℤ) ∣ W.Δ ∧ ¬ (q : ℤ) ∣ W.c₄) ∨
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ∀ τ ∈ A.inertiaSubgroupIn ℚ,
        ∀ (n : ℕ) (y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point), p ^ n • y = 0 → τ • y = y)
    (hpat : (¬ (p : ℤ) ∣ W.Δ ∧ ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∃ (x y : AlgebraicClosure ℚ)
          (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
          p • (Point.some x y h) = 0 ∧ x ∈ A)
      ∨ ((p : ℤ) ∣ W.Δ ∧ ¬ (p : ℤ) ∣ W.c₄)) :
    ¬ HasGaloisStableCofixedLine (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p := by
  classical

  rintro ⟨N, hNstab, hNbot, hNtop, hNcof⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  haveI := tw_isElliptic W hΔ

  have hcard : ∀ k : ℕ, Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point
      ((p ^ k : ℕ) : ℤ)) = p ^ (2 * k) := by
    intro k
    have h0 := WeierstrassCurve.card_torsion_of_isAlgClosed (K := AlgebraicClosure ℚ)
      (W.map (Int.castRingHom ℚ))
      (n := p ^ k) (Nat.cast_ne_zero.mpr (pow_ne_zero k hp.pos.ne'))
    rw [h0, ← pow_mul, mul_comm]
  have hcard1 : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point
      ((p : ℕ) : ℤ)) = p ^ 2 := by
    have := hcard 1
    rwa [pow_one, mul_one] at this

  set NA : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point :=
    N.toAddSubgroup.map (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point
      ((p : ℕ) : ℤ)).subtype.toAddMonoidHom with hNAdef
  have hNAmem : ∀ z : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      z ∈ NA ↔ ∃ n₀, n₀ ∈ N ∧ (n₀ : ((W.map
        (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = z := by
    intro z
    simp [hNAdef, AddSubgroup.mem_map]
  have hNAcard : Nat.card ↥NA = p := by
    have hinj : Function.Injective (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point
        ((p : ℕ) : ℤ)).subtype.toAddMonoidHom := Subtype.val_injective
    have e := AddSubgroup.equivMapOfInjective N.toAddSubgroup _ hinj
    rw [← Nat.card_congr e.toEquiv]
    exact tw_card_line hp hcard1 hNbot hNtop
  have hNAtor : ∀ z ∈ NA, p • z = 0 := by
    intro z hz
    obtain ⟨n₀, -, rfl⟩ := (hNAmem z).mp hz
    exact (tw_mem_tor p _).mp n₀.2
  have hNAstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ z ∈ NA, σ • z ∈ NA := by
    intro σ z hz
    obtain ⟨n₀, hn₀, rfl⟩ := (hNAmem z).mp hz
    exact (hNAmem _).mpr ⟨σ • n₀, hNstab σ n₀ hn₀, rfl⟩

  have hp' : p ∉ ({2, 3, 5, 7, 13} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

  have hCofNA : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ z, p • z = 0 → σ • z - z ∈ NA := by
    intro σ z hpz
    have hmem : z ∈ Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point
        ((p : ℕ) : ℤ) := (tw_mem_tor _ _).mpr hpz
    exact (hNAmem _).mpr ⟨σ • ⟨z, hmem⟩ - ⟨z, hmem⟩, hNcof σ ⟨z, hmem⟩, rfl⟩

  obtain ⟨e, he, heNA⟩ : ∃ e : ((W.map
      (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, p • e = 0 ∧ e ∉ NA := by
    have hex : ∃ t : ↥(Submodule.torsionBy ℤ ((W.map
        (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)), t ∉ N := by
      by_contra hall
      push Not at hall
      refine hNtop ?_
      rw [_root_.eq_top_iff]
      intro t _
      exact hall t
    obtain ⟨t, htN⟩ := hex
    refine ⟨(t : _), (tw_mem_tor p _).mp t.2, fun hmem => ?_⟩
    obtain ⟨n₀, hn₀, hn₀eq⟩ := (hNAmem _).mp hmem
    have hn₀t : n₀ = t := Subtype.ext hn₀eq
    rw [hn₀t] at hn₀
    exact htN hn₀


  have hdetN := WeierstrassCurve.smul_eq_det_smul_of_cofixed W p hΔ N hNcof hNtop

  have hcycNA : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ z ∈ NA, σ • z = ExtCitation.cycloExp p σ • z := by
    intro σ z hz
    obtain ⟨n₀, hn₀, rfl⟩ := (hNAmem z).mp hz
    have h1 := hdetN σ n₀ hn₀
    rw [tw_det_eq_cyclo W p hΔ σ, Nat.cast_smul_eq_nsmul] at h1
    calc σ • (n₀ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
        = ((σ • n₀ : Submodule.torsionBy ℤ ((W.map
            (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) : _) := rfl
      _ = ((ExtCitation.cycloExp p σ • n₀ : Submodule.torsionBy ℤ ((W.map
            (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) : _) := by
            rw [h1]
      _ = ExtCitation.cycloExp p σ • (n₀ : _) :=
            AddMonoidHom.map_nsmul (Submodule.torsionBy ℤ _ _).subtype.toAddMonoidHom _ _

  have hfrobNA : ∀ (q : ℕ), q.Prime → q ≠ p →
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime q →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ q →
      ∀ z ∈ NA, σ • z = ((q : ℕ) : ZMod p).val • z := by
    intro q hq hqp A hA σ hσ z hz
    obtain ⟨n₀, hn₀, rfl⟩ := (hNAmem z).mp hz
    have h1 := hdetN σ n₀ hn₀
    rw [tw_det_frob W p hΔ hq hqp A hA hσ] at h1
    rw [show ((q : ℕ) : ZMod p) = ((((q : ℕ) : ZMod p)).val : ZMod p) by
      rw [ZMod.natCast_val, ZMod.cast_id], Nat.cast_smul_eq_nsmul] at h1
    calc σ • (n₀ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
        = ((σ • n₀ : Submodule.torsionBy ℤ ((W.map
            (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) : _) := rfl
      _ = ((((q : ℕ) : ZMod p).val • n₀ : Submodule.torsionBy ℤ ((W.map
            (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) : _) := by
            rw [h1]
      _ = ((q : ℕ) : ZMod p).val • (n₀ : _) :=
            AddMonoidHom.map_nsmul (Submodule.torsionBy ℤ _ _).subtype.toAddMonoidHom _ _

  have hbadscal23 : ∀ q : ℕ, q = 2 ∨ q = 3 →
      ((q : ℕ) : ZMod p) ≠ 1 ∧ ((q : ℕ) : ZMod p) ≠ -1 := by
    intro q hq23
    haveI : NeZero p := ⟨hp.ne_zero⟩
    rcases hq23 with rfl | rfl
    · constructor
      · intro h
        have h1 : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
          rw [h]; norm_num
        have h2 : p ∣ 2 - 1 :=
          (Nat.modEq_iff_dvd' (by norm_num)).mp
            ((ZMod.natCast_eq_natCast_iff _ _ _).mp h1).symm
        have := Nat.le_of_dvd (by norm_num) h2
        omega
      · intro h
        have h1 : ((3 : ℕ) : ZMod p) = 0 := by
          have h' : (2 : ZMod p) = -1 := by exact_mod_cast h
          have h3 : ((3 : ℕ) : ZMod p) = (2 : ZMod p) + 1 := by push_cast; ring
          rw [h3, h']; ring
        rw [ZMod.natCast_eq_zero_iff] at h1
        have := Nat.le_of_dvd (by norm_num) h1
        omega
    · constructor
      · intro h
        have h1 : ((3 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
          rw [h]; norm_num
        have h2 : p ∣ 3 - 1 :=
          (Nat.modEq_iff_dvd' (by norm_num)).mp
            ((ZMod.natCast_eq_natCast_iff _ _ _).mp h1).symm
        have := Nat.le_of_dvd (by norm_num) h2
        omega
      · intro h
        have h1 : ((4 : ℕ) : ZMod p) = 0 := by
          have h' : (3 : ZMod p) = -1 := by exact_mod_cast h
          have h3 : ((4 : ℕ) : ZMod p) = (3 : ZMod p) + 1 := by push_cast; ring
          rw [h3, h']; ring
        rw [ZMod.natCast_eq_zero_iff] at h1
        have := Nat.le_of_dvd (by norm_num) h1
        omega

  have htoric : ∀ (q : ℕ), q.Prime → q ≠ p → (q : ℤ) ∣ W.Δ → ¬ (q : ℤ) ∣ W.c₄ →
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime q →
      ∀ (m : ℕ), 1 ≤ m →
      ∀ K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      Nat.card K = p ^ m → IsAddCyclic ↥K → (∀ x ∈ K, p ^ m • x = 0) →
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ K, σ • x ∈ K) →
      (∀ x ∈ K, p • x = 0 → x ∈ NA) → NA ≤ K →
      (∀ x ∈ K, p • x = 0 → W.InZeroComponentAt A x) ∧
        (∀ x, p ^ m • x = 0 → W.InZeroComponentAt A x → x ∈ K) := by

    have hR2at : ∀ (q : ℕ), q = 2 ∨ q = 3 → q.Prime → q ≠ p → (q : ℤ) ∣ W.Δ →
        ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime q →
        ∀ (m : ℕ), 1 ≤ m →
        ∀ K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        Nat.card K = p ^ m → IsAddCyclic ↥K → (∀ x ∈ K, p ^ m • x = 0) →
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ K, σ • x ∈ K) →
        (∀ x ∈ K, p • x = 0 → x ∈ NA) →
        (∀ x ∈ K, W.InZeroComponentAt A x) ∧
          (∀ x, p ^ m • x = 0 → W.InZeroComponentAt A x → x ∈ K) := by
      intro q h23 hq hqp hqΔ A hA m hm K hKcard hK1 hKtors hKstab hKdown
      have hqc₄ : ¬ (q : ℤ) ∣ W.c₄ := by
        rcases h23 with rfl | rfl
        · exact h2c₄
        · exact h3c₄
      obtain ⟨σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hq A hA
      obtain ⟨hc1, hc1'⟩ := hbadscal23 q h23
      refine AddSubgroup.inZeroComponentAt_of_cyclic_stable_scalar_dichotomy
        W A p m hm (hcard m) K hKcard hK1 hKtors σ (hKstab σ) hc1 hc1'
        ?_ ?_ ?_ ?_
      ·
        intro x hx hpx
        exact hfrobNA q hq hqp A hA σ hσ x (hKdown x hx hpx)
      ·
        intro x hx hout
        refine tw_dich W hq hΔ hqΔ hqc₄ A hA hσ.mem_decompositionSubgroup
          (n := p ^ m) (hpodd.pow) (Nat.one_lt_pow (by omega) hp.one_lt)
          (fun hdvd => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd)))
          x (hKtors x hx) hout
      ·
        intro x y _ _ hx hy
        exact WeierstrassCurve.inZeroComponentAt_sub W A hx hy
      ·
        exact tw_hM W hq hΔ hqΔ hqc₄ A hA p (fun h => hqp h.symm) hcard1
    intro q hq hqp hqΔ hqc₄ A hA m hm K hKcard hK1 hKtors hKstab hKdown hNAle
    by_cases _h23 : q = 2 ∨ q = 3
    ·
      obtain ⟨hKz, hzK⟩ := hR2at q _h23 hq hqp hqΔ A hA m hm K hKcard hK1 hKtors hKstab hKdown
      exact ⟨fun x hx _ => hKz x hx, hzK⟩
    ·
      exact m3c_escape W hΔ p hp2 hp' hcard1 NA hNAcard e he heNA
        (fun σ => hCofNA σ e he) h2Δ h2c₄ h3Δ h3c₄ hq hqp hqΔ
        hqc₄ A hA m hm K
        hKcard hK1 hKtors hKstab hKdown hNAle
        (fun A₂ hA₂ => hR2at 2 (Or.inl rfl) Nat.prime_two (by omega) h2Δ A₂ hA₂ m hm K
          hKcard hK1 hKtors hKstab hKdown)
        (fun A₃ hA₃ => hR2at 3 (Or.inr rfl) Nat.prime_three (by omega) h3Δ A₃ hA₃ m hm K
          hKcard hK1 hKtors hKstab hKdown)

  have hNontrivAt : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
      ∀ K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      NA ≤ K →
      ∃ τ ∈ A.inertiaSubgroupIn ℚ, ∃ x ∈ K, p • x = 0 ∧ τ • x ≠ x := by
    intro A hA K hNAle
    obtain ⟨τ, hτI, hdetτ⟩ := WeierstrassCurve.det_galoisRep_surjOn_inertia
      W p hΔ A hA (-1)
    have hy₀ : ∃ y₀, y₀ ∈ N ∧ y₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hNbot ((Submodule.eq_bot_iff N).mpr h)
    obtain ⟨y₀, hy₀N, hy₀ne⟩ := hy₀
    refine ⟨τ, hτI, (y₀ : _), hNAle ((hNAmem _).mpr ⟨y₀, hy₀N, rfl⟩),
      (tw_mem_tor p _).mp y₀.2, ?_⟩

    have h1 := hdetN τ y₀ hy₀N
    rw [hdetτ] at h1
    have h2 : τ • y₀ = -y₀ := by
      rw [h1, Units.val_neg, Units.val_one, neg_one_smul]
    intro heq

    have h2p : τ • ((y₀ : _)) = -((y₀ :
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) :=
      congrArg Subtype.val h2
    rw [heq] at h2p
    have h4 : ((y₀ : _)) + ((y₀ :
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) = 0 := by
      nth_rewrite 1 [h2p]
      exact neg_add_cancel _
    obtain ⟨k, hk⟩ := hpodd
    have hptor : p • ((y₀ : _)) =
        (0 : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) :=
      (tw_mem_tor p _).mp y₀.2

    have key : ∀ z : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        z + z = 0 → p • z = z := by
      intro z hz2
      have h2y : (2 : ℕ) • z = 0 := by rw [two_nsmul]; exact hz2
      rw [hk, add_nsmul, one_nsmul, mul_nsmul, h2y, nsmul_zero, zero_add]
    have h6 : ((y₀ : _)) =
        (0 : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := by
      rw [← key _ h4, hptor]
    exact hy₀ne (Subtype.ext h6)

  have hSpOfF : ∀ (m : ℕ), 1 ≤ m →
      ∀ K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      ∀ (cond : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point → Prop)
        (Fm FS : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
      (∀ x, x ∈ Fm ↔ p ^ m • x = 0 ∧ cond x) →
      (∀ x, x ∈ FS ↔ p ^ (m + 1) • x = 0 ∧ cond x) →
      K = Fm →
      (K ≤ FS ∧ (∀ x ∈ FS, p • x ∈ K) ∧
        ∀ x ∈ FS, ∀ e, p • e = 0 → x - e ∈ K → x ∈ K) := by
    intro m hm K cond Fm FS hFmiff hFSiff hKFm
    refine ⟨?_, ?_, ?_⟩
    ·
      intro x hx
      rw [hKFm] at hx
      obtain ⟨hxt, hxz⟩ := (hFmiff x).mp hx
      refine (hFSiff x).mpr ⟨?_, hxz⟩
      rw [pow_succ, mul_nsmul, hxt, nsmul_zero]
    ·
      intro x hx
      have hpx : p • x ∈ FS := AddSubgroup.nsmul_mem FS hx p
      obtain ⟨-, hxz⟩ := (hFSiff _).mp hpx
      have hxt' : p ^ m • (p • x) = 0 := by
        have h0 := ((hFSiff x).mp hx).1
        rw [← mul_nsmul, ← pow_succ']
        exact h0
      rw [hKFm]
      exact (hFmiff _).mpr ⟨hxt', hxz⟩
    ·
      intro x hx e hpe hxe
      have hFmle : Fm ≤ FS := by
        intro z hz
        obtain ⟨hzt, hzz⟩ := (hFmiff z).mp hz
        exact (hFSiff z).mpr ⟨by rw [pow_succ, mul_nsmul, hzt, nsmul_zero], hzz⟩
      have heFS : e ∈ FS := by
        have h1 : x - e ∈ FS := hFmle (hKFm ▸ hxe)
        have h2 := FS.sub_mem hx h1
        simpa using h2
      obtain ⟨-, hez⟩ := (hFSiff e).mp heFS
      have het : p ^ m • e = 0 := by
        obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        rw [hj, pow_succ', mul_nsmul, hpe, nsmul_zero]
      have heK : e ∈ K := by
        rw [hKFm]
        exact (hFmiff e).mpr ⟨het, hez⟩
      have hxsplit : x = (x - e) + e := (sub_add_cancel x e).symm
      rw [hxsplit]
      exact K.add_mem hxe heK

  have hEXT : ExtCitation.ExtVanishingCts p :=
    ExtCitation.extVanishingCts_of_three_le (by omega)

  have hSpAt : ∀ (m : ℕ), 1 ≤ m →
      ∀ K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      Nat.card K = p ^ m → IsAddCyclic ↥K → (∀ x ∈ K, p ^ m • x = 0) →
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ K, σ • x ∈ K) → NA ≤ K →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      ∃ F' : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ F', σ • x ∈ F') ∧
        K ≤ F' ∧ (∀ x ∈ F', p • x ∈ K) ∧ Nat.card F' = p ^ (m + 1) ∧
        ∀ x ∈ F', ∀ e, p • e = 0 → x - e ∈ K → x ∈ K := by
    intro m hm K hKcard hK1 hKtors hKstab hNAle A hA
    rcases hpat with ⟨hpΔ', hordAll⟩ | ⟨hpΔ, hpc₄⟩
    ·
      have hord := hordAll A hA
      obtain ⟨Fm, hFmiff, hFmcard, hFmD, hFmabs⟩ :=
        WeierstrassCurve.exists_atP_filtration_of_goodReduction
          W p hp2 hpΔ' A hA hord m hm
      obtain ⟨FS, hFSiff, hFScard, hFSD, hFSabs⟩ :=
        WeierstrassCurve.exists_atP_filtration_of_goodReduction
          W p hp2 hpΔ' A hA hord (m + 1) (by omega)
      haveI : Finite ↥Fm := Nat.finite_of_card_ne_zero (hFmcard ▸ pow_ne_zero _ hp.pos.ne')
      have hKFm : K = Fm := by
        refine tw_addSubgroup_eq_of_le_of_card_eq ?_ (by rw [hKcard, hFmcard])
        exact AddSubgroup.eq_atP_filtration_of_cyclic_stable_inertia_nontrivial
          W p A hA m hm K hKcard hK1 hKtors
          (fun σ _ x hx => hKstab σ x hx) (hNontrivAt A hA K hNAle) Fm hFmabs
      obtain ⟨hle, hdown, hsep⟩ := hSpOfF m hm K _ Fm FS hFmiff hFSiff hKFm
      exact ⟨FS, hFSD, hle, hdown, hFScard, hsep⟩
    ·
      obtain ⟨Fm, hFmiff, hFmcard, hFmD, hFmabs⟩ :=
        WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction
          W p hp2 hΔ hpΔ hpc₄ A hA m hm
      obtain ⟨FS, hFSiff, hFScard, hFSD, hFSabs⟩ :=
        WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction
          W p hp2 hΔ hpΔ hpc₄ A hA (m + 1) (by omega)
      haveI : Finite ↥Fm := Nat.finite_of_card_ne_zero (hFmcard ▸ pow_ne_zero _ hp.pos.ne')
      have hKFm : K = Fm := by
        refine tw_addSubgroup_eq_of_le_of_card_eq ?_ (by rw [hKcard, hFmcard])
        exact AddSubgroup.eq_atP_filtration_of_cyclic_stable_inertia_nontrivial
          W p A hA m hm K hKcard hK1 hKtors
          (fun σ _ x hx => hKstab σ x hx) (hNontrivAt A hA K hNAle) Fm hFmabs
      obtain ⟨hle, hdown, hsep⟩ := hSpOfF m hm K _ Fm FS hFmiff hFSiff hKFm
      exact ⟨FS, hFSD, hle, hdown, hFScard, hsep⟩

  have hInv : ∀ m : ℕ, 1 ≤ m →
      ∃ K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        Nat.card K = p ^ m ∧ IsAddCyclic ↥K ∧ (∀ x ∈ K, p ^ m • x = 0) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ K, σ • x ∈ K) ∧
        (∀ x ∈ K, p • x = 0 → x ∈ NA) ∧ NA ≤ K := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases hm0 : m = 0
      ·
        subst hm0
        haveI : Finite ↥NA := Nat.finite_of_card_ne_zero (hNAcard ▸ hp.pos.ne')
        refine ⟨NA, by rw [pow_one]; exact hNAcard, ?_, ?_, hNAstab,
          fun x hx _ => hx, le_refl NA⟩
        · exact isAddCyclic_of_prime_card (p := p) hNAcard
        · intro x hx
          rw [pow_one]
          exact hNAtor x hx
      ·
        obtain ⟨K, hKcard, hK1, hKtors, hKstab, hKdown, hNAle⟩ := ih (by omega)
        have hm1 : 1 ≤ m := by omega
        have hCof : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
            ∀ e, p • e = 0 → σ • e - e ∈ K := by
          intro σ e hpe
          have hmem : e ∈ Submodule.torsionBy ℤ
              ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point
              ((p : ℕ) : ℤ) := (tw_mem_tor _ _).mpr hpe
          exact hNAle ((hNAmem _).mpr ⟨σ • ⟨e, hmem⟩ - ⟨e, hmem⟩, hNcof σ ⟨e, hmem⟩, rfl⟩)
        have hCyc : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
            ∀ x ∈ K, p • x = 0 → σ • x = ExtCitation.cycloExp p σ • x :=
          fun σ x hx hpx => hcycNA σ x (hKdown x hx hpx)
        have hU : ∀ ℓ' : ℕ, ℓ'.Prime → ℓ' ≠ p →
            ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ' →
            ∀ τ ∈ A.inertiaSubgroupIn ℚ,
            ∀ y, p • y ∈ K → τ • y - y ∈ K := by
          intro ℓ' hℓ' hℓ'p A hA τ hτ y hpy
          have hytor : p ^ (m + 1) • y = 0 := by
            rw [pow_succ', mul_nsmul]
            exact hKtors _ hpy
          rcases hloc ℓ' hℓ' hℓ'p with hℓΔ | ⟨hℓΔ, hqc₄'⟩ | htriv
          ·
            have hfix := tw_unramified_good W hℓ' hℓΔ A hA hτ
              (n := p ^ (m + 1))
              (fun hdvd => hℓ'p ((Nat.prime_dvd_prime_iff_eq hℓ' hp).mp
                (hℓ'.dvd_of_dvd_pow hdvd)))
              y hytor
            rw [hfix, sub_self]
            exact K.zero_mem
          ·
            obtain ⟨hKz, hzK⟩ := htoric ℓ' hℓ' hℓ'p hℓΔ hqc₄' A hA m hm1 K
              hKcard hK1 hKtors hKstab hKdown hNAle

            have hdz : W.InZeroComponentAt A (τ • y - y) :=
              WeierstrassCurve.inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
                W hℓ' hΔ hℓΔ hqc₄' A hA τ hτ y

            have hpmyK : p ^ m • y ∈ K := by
              obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
              rw [hj, pow_succ', mul_nsmul]
              exact AddSubgroup.nsmul_mem K hpy _
            have hpmyt : p • (p ^ m • y) = 0 := by
              rw [← mul_nsmul, ← pow_succ]
              exact hytor
            obtain ⟨M, hMiff, -, hMfix⟩ :=
              WeierstrassCurve.exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
                W hℓ' hΔ hℓΔ hqc₄' A hA (ℓ := p) hp
            have hinM : (⟨p ^ m • y, (tw_mem_tor _ _).mpr hpmyt⟩ :
                ↥(Submodule.torsionBy ℤ _ ((p : ℕ) : ℤ))) ∈ M :=
              (hMiff _).mpr (hKz _ hpmyK hpmyt)
            have hfixy := hMfix (fun h => hℓ'p h.symm) τ hτ _ hinM
            have hfixy' : τ • (p ^ m • y) = p ^ m • y := congrArg Subtype.val hfixy
            have hdtor : p ^ m • (τ • y - y) = 0 := by
              have hcomm : p ^ m • (τ • y) = τ • (p ^ m • y) := by
                rw [← natCast_zsmul y, WeierstrassCurve.Affine.Point.algEquiv_smul_zsmul,
                  natCast_zsmul]
              rw [nsmul_sub, hcomm, hfixy', sub_self]
            exact hzK _ hdtor hdz
          ·
            rw [htriv A hA τ hτ (m + 1) y hytor, sub_self]
            exact K.zero_mem
        obtain ⟨K', hKK', hK'card, hK'tors, hK'stab, hK'down1⟩ :=
          AddSubgroup.exists_towerStep_of_extVanishingCts W p hΔ hcard m hm1 K
            hKcard hK1 hKtors hKstab hCof hCyc hU
            (hSpAt m hm1 K hKcard hK1 hKtors hKstab hNAle) hEXT

        haveI : Finite ↥K' := Nat.finite_of_card_ne_zero (hK'card ▸ pow_ne_zero _ hp.pos.ne')
        haveI : Finite ↥NA := Nat.finite_of_card_ne_zero (hNAcard ▸ hp.pos.ne')
        have hK'cyc : IsAddCyclic ↥K' := by
          have hexp : ∀ x : ↥K', p ^ (m + 1) • x = 0 := by
            intro x
            exact Subtype.ext (hK'tors x.1 x.2)
          have hmapNA : ∀ s : {x : ↥K' // p • x = 0},
              ((s.1 : _) : ((W.map
                (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) ∈ NA := by
            intro s
            have pv : p • ((s.1 : _) : ((W.map
                (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 :=
              congrArg Subtype.val s.2
            exact hKdown _ (hK'down1 _ s.1.2 pv) pv
          have hsocle : Nat.card {x : ↥K' // p • x = 0} ≤ p := by
            have hinj : Function.Injective (fun s : {x : ↥K' // p • x = 0} =>
                (⟨(s.1 : _), hmapNA s⟩ : ↥NA)) := by
              intro a b hab
              have hab' : (⟨(a.1 : _), hmapNA a⟩ : ↥NA) = ⟨(b.1 : _), hmapNA b⟩ := hab
              have hv : ((a.1 : _) : ((W.map
                  (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = ((b.1 : _)) :=
                congrArg (fun z : ↥NA => (z : ((W.map
                  (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) hab'
              exact Subtype.ext (Subtype.ext hv)
            calc Nat.card {x : ↥K' // p • x = 0} ≤ Nat.card ↥NA :=
                  Nat.card_le_card_of_injective _ hinj
              _ = p := hNAcard
          exact (IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow hp (m + 1)
            hexp hsocle).1
        refine ⟨K', hK'card, hK'cyc, hK'tors, hK'stab, ?_, le_trans hNAle hKK'⟩
        intro x hx hpx
        exact hKdown x (hK'down1 x hx hpx) hpx

  obtain ⟨ℓ₀, hℓ₀ge, hℓ₀p⟩ :=
    Nat.exists_infinite_primes ((2 * W.Δ * p).natAbs + 1)
  have h2abcp : (2 * W.Δ * p : ℤ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero hΔ) (by exact_mod_cast hp.ne_zero)
  have hℓ₀nd : ¬ (ℓ₀ : ℤ) ∣ 2 * W.Δ * p := by
    intro hdvd
    have h1 : ℓ₀ ∣ (2 * W.Δ * p).natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hdvd
      rwa [Int.natAbs_natCast] at this
    have h2 : ℓ₀ ≤ (2 * W.Δ * p).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr h2abcp) h1
    omega
  have hℓ₀ne2 : ℓ₀ ≠ 2 := by
    intro h
    refine hℓ₀nd ?_
    rw [h]
    exact ⟨W.Δ * p, by push_cast; ring⟩
  have hℓ₀nep : ℓ₀ ≠ p := by
    intro h
    refine hℓ₀nd ?_
    rw [h]
    exact ⟨2 * W.Δ, by ring⟩
  have hℓ₀good : ¬ (ℓ₀ : ℤ) ∣ W.Δ := by
    intro h
    refine hℓ₀nd ?_
    obtain ⟨c, hc⟩ := h
    exact ⟨2 * c * p, by rw [hc]; ring⟩

  haveI : Fact ℓ₀.Prime := ⟨hℓ₀p⟩
  haveI hfinW : Finite ((W⁄(ZMod ℓ₀))).Point :=
    WeierstrassCurve.Affine.Point.finite_of_finite_field _
  haveI : Nonempty ((W⁄(ZMod ℓ₀))).Point := ⟨0⟩
  have hN₀pos : 0 < Nat.card ((W⁄(ZMod ℓ₀))).Point := Nat.card_pos
  have hN₀lt : Nat.card ((W⁄(ZMod ℓ₀))).Point
      < p ^ Nat.card ((W⁄(ZMod ℓ₀))).Point :=
    Nat.lt_pow_self hp.one_lt
  set N₀ : ℕ := Nat.card ((W⁄(ZMod ℓ₀))).Point with hN₀def

  obtain ⟨K, hKcard, hK1, hKtors, hKstab, hKdown, hNAle⟩ := hInv N₀ hN₀pos

  have hopen := WeierstrassCurve.isOpen_torsionBy_fixingSubgroup
    W (p ^ N₀) hΔ (pow_pos hp.pos _)
  have hInert : ∀ ℓ' : ℕ, ℓ'.Prime →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ' →
      ∀ τ ∈ A.inertiaSubgroupIn ℚ,
      ∀ y, p ^ N₀ • y = 0 → τ • y - y ∈ K := by
    intro ℓ' hℓ' A hA τ hτ y hytor
    by_cases hℓ'p : ℓ' = p
    ·
      subst ℓ'
      rcases hpat with ⟨hpΔ', hordAll⟩ | ⟨hpΔ, hpc₄⟩
      ·
        have hord := hordAll A hA
        obtain ⟨Fm, hFmiff, hFmcard, hFmD, hFmabs⟩ :=
          WeierstrassCurve.exists_atP_filtration_of_goodReduction
            W p hp2 hpΔ' A hA hord N₀ hN₀pos
        haveI : Finite ↥Fm := Nat.finite_of_card_ne_zero (hFmcard ▸ pow_ne_zero _ hp.pos.ne')
        have hKFm : K = Fm := by
          refine tw_addSubgroup_eq_of_le_of_card_eq ?_ (by rw [hKcard, hFmcard])
          exact AddSubgroup.eq_atP_filtration_of_cyclic_stable_inertia_nontrivial
            W p A hA N₀ hN₀pos K hKcard hK1 hKtors
            (fun σ _ x hx => hKstab σ x hx) (hNontrivAt A hA K hNAle) Fm hFmabs
        rw [hKFm]
        exact hFmabs τ hτ y hytor
      ·
        obtain ⟨Fm, hFmiff, hFmcard, hFmD, hFmabs⟩ :=
          WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction
            W p hp2 hΔ hpΔ hpc₄ A hA N₀ hN₀pos
        haveI : Finite ↥Fm := Nat.finite_of_card_ne_zero (hFmcard ▸ pow_ne_zero _ hp.pos.ne')
        have hKFm : K = Fm := by
          refine tw_addSubgroup_eq_of_le_of_card_eq ?_ (by rw [hKcard, hFmcard])
          exact AddSubgroup.eq_atP_filtration_of_cyclic_stable_inertia_nontrivial
            W p A hA N₀ hN₀pos K hKcard hK1 hKtors
            (fun σ _ x hx => hKstab σ x hx) (hNontrivAt A hA K hNAle) Fm hFmabs
        rw [hKFm]
        exact hFmabs τ hτ y hytor
    ·
      rcases hloc ℓ' hℓ' hℓ'p with hℓΔ | ⟨hℓΔ, hqc₄'⟩ | htriv
      ·
        have hfix := tw_unramified_good W hℓ' hℓΔ A hA hτ
          (n := p ^ N₀)
          (fun hdvd => hℓ'p ((Nat.prime_dvd_prime_iff_eq hℓ' hp).mp
            (hℓ'.dvd_of_dvd_pow hdvd)))
          y hytor
        rw [hfix, sub_self]
        exact K.zero_mem
      ·
        obtain ⟨hKz, hzK⟩ := htoric ℓ' hℓ' hℓ'p hℓΔ hqc₄' A hA N₀ hN₀pos K
          hKcard hK1 hKtors hKstab hKdown hNAle
        have hdz : W.InZeroComponentAt A (τ • y - y) :=
          WeierstrassCurve.inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
            W hℓ' hΔ hℓΔ hqc₄' A hA τ hτ y
        have hdtor : p ^ N₀ • (τ • y - y) = 0 := by
          have hcomm : p ^ N₀ • (τ • y) = τ • (p ^ N₀ • y) := by
            rw [← natCast_zsmul y, WeierstrassCurve.Affine.Point.algEquiv_smul_zsmul,
              natCast_zsmul]
          rw [nsmul_sub, hcomm, hytor, sub_zero]
          rfl
        exact hzK _ hdtor hdz
      ·
        rw [htriv A hA τ hτ (N₀) y hytor, sub_self]
        exact K.zero_mem
  have hGal := AddSubgroup.galois_trivial_quotient_of_inertia_absorbing
    W p N₀ hN₀pos K hopen hInert

  obtain ⟨A₀, hA₀, σ₀, hσ₀⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ₀ hℓ₀p
  have hℓ₀ndvd : ¬ ℓ₀ ∣ p ^ N₀ := fun hdvd =>
    hℓ₀nep ((Nat.prime_dvd_prime_iff_eq hℓ₀p hp).mp (hℓ₀p.dvd_of_dvd_pow hdvd))
  have hN₀K : ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ N₀ • y = 0 → (N₀ : ℤ) • y ∈ K := by
    intro y hytor
    have hd₁ : σ₀ • y - y ∈ K := hGal σ₀ y hytor
    have hcommN : p ^ N₀ • (σ₀ • y) = 0 := by
      have h2 : σ₀ • (p ^ N₀ • y) = p ^ N₀ • (σ₀ • y) := by
        rw [← natCast_zsmul y, WeierstrassCurve.Affine.Point.algEquiv_smul_zsmul, natCast_zsmul]
      rw [← h2, hytor]
      rfl
    have hd₂ : σ₀ • (σ₀ • y) - σ₀ • y ∈ K := hGal σ₀ _ hcommN
    have hCHy0 := WeierstrassCurve.frobenius_cayleyHamilton_on_torsion W ℓ₀ hℓ₀p
      hℓ₀good A₀ hA₀ σ₀ hσ₀ (p ^ N₀) (pow_pos hp.pos _) hℓ₀ndvd y hytor
    have hCHy : σ₀ • σ₀ • y + (ℓ₀ : ℤ) • y
        = ((ℓ₀ : ℤ) + 1 - (N₀ : ℤ)) • (σ₀ • y) := hCHy0
    have hexp : ((ℓ₀ : ℤ) + 1 - (N₀ : ℤ)) • (σ₀ • y)
        = (ℓ₀ : ℤ) • (σ₀ • y) + σ₀ • y - (N₀ : ℤ) • (σ₀ • y) := by
      rw [sub_smul, add_smul, one_smul]
    rw [hexp] at hCHy
    have hkey : (N₀ : ℤ) • (σ₀ • y)
        = (ℓ₀ : ℤ) • (σ₀ • y - y) - (σ₀ • σ₀ • y - σ₀ • y) := by
      have h2 : σ₀ • σ₀ • y
          = (ℓ₀ : ℤ) • (σ₀ • y) + σ₀ • y - (N₀ : ℤ) • (σ₀ • y) - (ℓ₀ : ℤ) • y :=
        eq_sub_of_add_eq hCHy
      rw [zsmul_sub, h2]
      abel
    have hS1 : (N₀ : ℤ) • (σ₀ • y) ∈ K := by
      rw [hkey]
      exact K.sub_mem (AddSubgroup.zsmul_mem K hd₁ _) hd₂
    have hfinal : (N₀ : ℤ) • y = (N₀ : ℤ) • (σ₀ • y) - (N₀ : ℤ) • (σ₀ • y - y) := by
      rw [zsmul_sub]
      abel
    rw [hfinal]
    exact K.sub_mem hS1 (AddSubgroup.zsmul_mem K hd₁ _)

  have hEpNA : ∀ e : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p • e = 0 → e ∈ NA := by
    intro e hpe

    have hsplit : ∀ n : ℕ, 0 < n → ∃ t u : ℕ, n = p ^ t * u ∧ ¬ p ∣ u := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro hn
        by_cases hdvd : p ∣ n
        · obtain ⟨m', hm'⟩ := hdvd
          have hm'pos : 0 < m' := by
            rcases Nat.eq_zero_or_pos m' with h | h
            · rw [h, mul_zero] at hm'
              omega
            · exact h
          have hm'lt : m' < n := by
            have h2 : 2 * m' ≤ p * m' := Nat.mul_le_mul_right m' hp.two_le
            omega
          obtain ⟨t', u, hu, hpu⟩ := ih m' hm'lt hm'pos
          refine ⟨t' + 1, u, ?_, hpu⟩
          rw [hm', hu, pow_succ]
          ring
        · exact ⟨0, n, by rw [pow_zero, one_mul], hdvd⟩
    obtain ⟨t, u, hNsplit, hpu⟩ := hsplit N₀ hN₀pos
    have htlt : t < N₀ := by
      have h1 : p ^ t ∣ N₀ := Dvd.intro u hNsplit.symm
      have h2 : p ^ t ≤ N₀ := Nat.le_of_dvd hN₀pos h1
      have h3 : p ^ t < p ^ N₀ := lt_of_le_of_lt h2 hN₀lt
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp h3

    obtain ⟨y, hy1, hy2⟩ := tw_psmul_surj p hp t (hcard (t + 1)) (hcard t) (hcard 1) e hpe
    have hyN : p ^ N₀ • y = 0 := by
      obtain ⟨d, hd⟩ : ∃ d, N₀ = (t + 1) + d := ⟨N₀ - (t + 1), by omega⟩
      rw [hd, pow_add, mul_nsmul, hy1, nsmul_zero]
    have hNyK : (N₀ : ℤ) • y ∈ K := hN₀K y hyN

    have hNue : (N₀ : ℤ) • y = u • e := by
      rw [natCast_zsmul, hNsplit, mul_nsmul, hy2]
    have hueK : u • e ∈ K := hNue ▸ hNyK
    have hpue : p • (u • e) = 0 := by
      rw [← mul_nsmul, mul_comm, mul_nsmul, hpe, nsmul_zero]
    have hueNA : u • e ∈ NA := hKdown _ hueK hpue

    have hcop : Nat.gcd u p = 1 := Nat.Coprime.gcd_eq_one
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpu).symm
    have hbez := Nat.gcd_eq_gcd_ab u p
    rw [hcop] at hbez
    have he : e = (Nat.gcdA u p) • ((u : ℤ) • e) + (Nat.gcdB u p) • ((p : ℤ) • e) := by
      calc e = (1 : ℤ) • e := (one_smul ℤ e).symm
        _ = ((u : ℤ) * Nat.gcdA u p + (p : ℤ) * Nat.gcdB u p) • e := by
            rw [← hbez]; norm_num
        _ = (Nat.gcdA u p) • ((u : ℤ) • e) + (Nat.gcdB u p) • ((p : ℤ) • e) := by
            rw [mul_comm (u : ℤ), mul_comm (p : ℤ), add_zsmul, mul_zsmul, mul_zsmul]
    rw [he]
    have h1 : (u : ℤ) • e ∈ NA := by
      rw [natCast_zsmul]
      exact hueNA
    have h2 : (p : ℤ) • e = 0 := by
      rw [natCast_zsmul]
      exact hpe
    refine AddSubgroup.add_mem NA (AddSubgroup.zsmul_mem NA h1 _) ?_
    rw [h2, zsmul_zero]
    exact NA.zero_mem

  haveI : Finite ↥(Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero (hcard1 ▸ pow_ne_zero _ hp.pos.ne')
  haveI : Finite ↥NA := Nat.finite_of_card_ne_zero (hNAcard ▸ hp.pos.ne')
  have hmapE : ∀ s : ↥(Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)),
      ((s : _) : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) ∈ NA :=
    by
    intro s
    exact hEpNA _ ((tw_mem_tor p _).mp s.2)
  have hinj2 : Function.Injective (fun s : ↥(Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) =>
      (⟨(s : _), hmapE s⟩ : ↥NA)) := by
    intro a b hab
    have hab' : (⟨(a : _), hmapE a⟩ : ↥NA) = ⟨(b : _), hmapE b⟩ := hab
    have hv : ((a : _) : ((W.map
        (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = ((b : _)) :=
      congrArg (fun z : ↥NA => (z : ((W.map
        (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) hab'
    exact Subtype.ext hv
  have hle2 : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card ↥(Submodule.torsionBy ℤ
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point
          ((p : ℕ) : ℤ)) := hcard1.symm
      _ ≤ Nat.card ↥NA := Nat.card_le_card_of_injective _ hinj2
      _ = p := hNAcard
  have hple1 : p ≤ 1 := by
    rw [pow_two] at hle2
    exact Nat.le_of_mul_le_mul_left (by omega) hp.pos
  have := hp.two_le
  omega

end MazurP23
