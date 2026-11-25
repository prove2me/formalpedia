-- Prove2me | solution 1 for GlobalTheory.DegCnt.FlagDisc.idx_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:54:25.962806+00:00
-- url     : https://prove2.me/submissions/197bc9de-2326-4a7b-bbac-5da2d5703ea3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinor
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_mem_dual_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FlagDisc
open GlobalTheory.DegCnt.DelScale GlobalTheory.DegCnt.Absorb
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.FlagDisc
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (x x' : ι → V) (hx : Set.range x' = Set.range x)
    (hi : ∀ p q, H.B (x p) (x' q) ∈ (1 : Submodule (𝓞 K) K))
    (hd : (Matrix.of fun p q => H.B (x p) (x' q)).det ≠ 0) :
    (∀ v ∈ Submodule.span K (Set.range x), (∀ q, H.B v (x' q) = 0) → v = 0) ∧
    (idx (dual H (Submodule.span (𝓞 K) (Set.range x))) (Submodule.span (𝓞 K) (Set.range x)) : ℝ) =
      |((Algebra.norm ℚ (Matrix.of fun p q => H.B (x p) (x' q)).det : ℚ) : ℝ)| := by
  set G : Matrix ι ι K := Matrix.of fun p q => H.B (x p) (x' q) with hG
  have hu : IsUnit G.det := hd.isUnit
  choose g hg using fun p q => Submodule.mem_one.1 (hi p q)
  have eg : (algebraMap (𝓞 K) K).mapMatrix (Matrix.of g) = G := by
    ext p q; simp [hg, hG]
  have ed : algebraMap (𝓞 K) K (Matrix.of g).det = G.det := by rw [RingHom.map_det, eg]
  set u : ι → V := fun p => ∑ q, G⁻¹ p q • x q with hu'
  have pair : ∀ (c : ι → K) q, H.B (∑ p, c p • x p) (x' q) = Matrix.vecMul c G q := by
    intro c q
    simp [Matrix.vecMul, dotProduct, hG, LinearMap.sum_apply]
  have comb : ∀ c : ι → K, ∑ p, c p • u p = ∑ p, Matrix.vecMul c G⁻¹ p • x p := by
    intro c
    simp only [hu', Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have pu : ∀ (c : ι → K) q, H.B (∑ p, c p • u p) (x' q) = c q := by
    intro c q
    rw [comb, pair, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have rep : ∀ v ∈ Submodule.span K (Set.range x), v = ∑ p, H.B v (x' p) • u p := by
    intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
    rw [comb]
    simp only [pair]
    rw [show (fun p => Matrix.vecMul c G p) = Matrix.vecMul c G from rfl, Matrix.vecMul_vecMul,
      Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
  have li : LinearIndependent K u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc q
    rw [← pu c q, hc]; simp
  refine ⟨fun v hv h0 => by rw [rep v hv]; simp [h0], ?_⟩
  have hdual : dual H (Submodule.span (𝓞 K) (Set.range x)) = Submodule.span (𝓞 K) (Set.range u) := by
    ext v
    rw [mem_dual_iff, Submodule.span_span_of_tower]
    constructor
    · rintro ⟨h1, h2⟩
      rw [rep v h1]
      refine Submodule.sum_mem _ fun p _ => ?_
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h2 (x' p) (Submodule.subset_span (hx ▸ ⟨p, rfl⟩)))
      rw [← ha, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
    · intro hv
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
      have e : ∑ p, c p • u p = ∑ p, (fun p => algebraMap (𝓞 K) K (c p)) p • u p := by
        simp only [algebraMap_smul]
      rw [e]
      refine ⟨?_, fun w hw => ?_⟩
      · rw [comb]
        exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
      · rw [← hx] at hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨q, rfl⟩ := hw
          rw [pu]
          exact Submodule.mem_one.2 ⟨_, rfl⟩
        | zero => rw [map_zero]; exact zero_mem _
        | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
        | smul a b _ hb =>
          rw [← algebraMap_smul K a b, LinearMap.map_smulₛₗ]
          exact Submodule.smul_mem _ (sig K a) hb
  rw [hdual, idx, GlobalTheory.relIndex_span_eq_natAbs_norm_det li (g := Matrix.of g) (fun e => hd (by rw [← ed, e, map_zero]))
    (fun p => ?_), ← ed]
  · have := Algebra.coe_norm_int (Matrix.of g).det
    rw [RingOfIntegers.coe_eq_algebraMap] at this
    rw [← this, Nat.cast_natAbs]
    simp
  · rw [rep (x p) (Submodule.subset_span ⟨p, rfl⟩)]
    simp only [← hg, algebraMap_smul, Matrix.of_apply]
end GlobalTheory.DegCnt.FlagDisc
