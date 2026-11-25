-- Prove2me | solution 1 for GlobalTheory.eq_on_rankOneCurve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:59:31.25167+00:00
-- url     : https://prove2.me/submissions/a1f63b99-9e4b-4124-a139-c8dac546fb7b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
import Theorems.Thm_GlobalTheory_rankOneCurve_mem
import Theorems.Thm_GlobalTheory_eq_on_rankOneCurve_of_integral
import Theorems.Thm_GlobalTheory_tendsto_floor_nat_mul_div
import Theorems.Thm_GlobalTheory_isOpen_phDom
import Theorems.Thm_GlobalTheory_of_symm_mem_phDom
import Theorems.Thm_GlobalTheory_phSym_eq_self_of_isSymm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
open GlobalTheory
variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}
variable {e : Fin g} {Z : Matrix (Fin g) (Fin g) ℂ} (hZs : Z.IsSymm) (hZe : ∀ i, Z i e = 0)
  (hZ : ∀ u : Fin g → ℝ, u e = 1 → ∀ y : ℝ, 0 < y →
    (Z.map Complex.im + y • vecMulVec u u).PosDef)
include hZs hZe hZ
namespace GlobalTheory
theorem _root_.solution (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    {u v : Fin g → ℝ} (hu : u e = 1) (hv : v e = 0) (z w : ℍ) :
    H (rankOneCurve Z (vecMulVec (Pi.single e 1) v + vecMulVec v (Pi.single e 1)) u z) =
      H (rankOneCurve Z (vecMulVec (Pi.single e 1) v + vecMulVec v (Pi.single e 1)) u w) := by
  let R : (Fin g → ℝ) → Matrix (Fin g) (Fin g) ℝ := fun v =>
    vecMulVec (Pi.single e 1) v + vecMulVec v (Pi.single e 1)
  have hR : ∀ v, (R v).IsSymm := fun v => by
    ext i j
    simp only [R, transpose_apply, Matrix.add_apply, vecMulVec_apply]
    ring
  let a : (Fin g → ℝ) → ℕ → Fin g → ℝ := fun x n i => (⌊(n + 1 : ℝ) * x i⌋ : ℝ) / (n + 1)
  have hau : ∀ n, a u n e = 1 := fun n => by
    have : ⌊(n + 1 : ℝ)⌋ = n + 1 := by exact_mod_cast Int.floor_intCast (R := ℝ) (n + 1)
    simp only [a, hu, mul_one, this]
    push_cast
    exact div_self (by positivity)
  have hav : ∀ n, a v n e = 0 := fun n => by simp [a, hv]
  have ha : ∀ x (n : ℕ) i, ((n + 1 : ℕ) : ℝ) * a x n i ∈ (Int.castRingHom ℝ).range := by
    intro x n i
    refine ⟨⌊(n + 1 : ℝ) * x i⌋, ?_⟩
    simp only [a, eq_intCast]
    push_cast
    field_simp
  have hε : ∀ i, (Pi.single e 1 : Fin g → ℝ) i ∈ (Int.castRingHom ℝ).range := fun i => by
    by_cases h : i = e <;> simp [h]
  have hlim : ∀ z : ℍ, Filter.Tendsto (fun n => H (rankOneCurve Z (R (a v n)) (a u n) z))
      Filter.atTop (𝓝 (H (rankOneCurve Z (R v) u z))) := by
    intro z
    have hm := rankOneCurve_mem hZs hZ (hR v) hu z.im_pos
    have hc : Continuous fun p : (Fin g → ℝ) × (Fin g → ℝ) =>
        (of.symm (rankOneCurve Z (R p.1) p.2 z) : Fin g → Fin g → ℂ) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [rankOneCurve, of_symm_apply, of_apply, R, Matrix.add_apply, vecMulVec_apply]
      fun_prop
    have h1 : Filter.Tendsto (fun n => (a v n, a u n)) Filter.atTop (𝓝 (v, u)) :=
      (tendsto_pi_nhds.2 fun i => tendsto_floor_nat_mul_div _).prodMk_nhds
        (tendsto_pi_nhds.2 fun i => tendsto_floor_nat_mul_div _)
    have h2 := (hol.continuousOn.continuousAt
      ((isOpen_phDom g).mem_nhds (of_symm_mem_phDom hm))).tendsto.comp
      ((hc.tendsto (v, u)).comp h1)
    simp only [Equiv.apply_symm_apply, phSym_eq_self_of_isSymm hm.1] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply, Equiv.apply_symm_apply,
      phSym_eq_self_of_isSymm (rankOneCurve_mem hZs hZ (hR _) (hau n) z.im_pos).1]
  refine tendsto_nhds_unique (hlim z) ((hlim w).congr fun n => ?_)
  refine eq_on_rankOneCurve_of_integral hZs hZe hZ hol hH hb (Nat.succ_ne_zero n) (hau n) (hR _)
    (by simp [R, vecMulVec_apply, hav]) (ha u n) (fun i => ?_) (fun i j => ?_) w z
  · simpa [R, vecMulVec_apply, hav] using ha v n i
  · convert mul_mem (natCast_mem _ (n + 1))
      (add_mem (mul_mem (hε i) (ha v n j)) (mul_mem (ha v n i) (hε j))) using 1
    simp only [R, Matrix.add_apply, vecMulVec_apply]
    ring
end GlobalTheory
