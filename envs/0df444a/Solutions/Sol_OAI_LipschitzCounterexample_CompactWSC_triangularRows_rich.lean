-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.triangularRows_rich
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:48:03.70981+00:00
-- url     : https://prove2.me/submissions/4192c149-7728-4412-a06f-bd290f3766f3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SmoothRows.lean:L112-L159
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.triangularRows_rich. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothCalculus
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_EnergyEstimates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_exists_smooth_finite_approx
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_exists_molecular_approx
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_exists_triangular_duals

-- ---- from OAI.Analysis.LipschitzEquivalence.SmoothRows ----
namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSpace
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSpace
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSubtypeSpaceMemSubmoduleRealSupported
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSubtypeSpaceMemSubmoduleSupported
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeSpaceMemSubmoduleSupported
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealContinuousLinearMapIdSubtypeSpaceMemSubmoduleSupported
theorem dual_molecular {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (a : MolecularData H) (T : Space H →L[ℝ] ℝ) :
    T a.vector = molPair a (fun p => T (point p)) := by
  simp only [MolecularData.vector,map_sum,map_smul,map_sub,smul_eq_mul,molPair,LinearMap.coe_mk,AddHom.coe_mk]

theorem molPair_approx {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (a : MolecularData H) (f g : H → ℝ) {δ : ℝ}
    (hp : ∀ i, |f (a.p i)-g (a.p i)| ≤ δ)
    (hq : ∀ i, |f (a.q i)-g (a.q i)| ≤ δ) :
    |molPair a f-molPair a g| ≤ 2*δ*(∑ i, |a.coeff i|) := by
  change |(∑ i, a.coeff i*(f (a.p i)-f (a.q i)))-∑ i, a.coeff i*(g (a.p i)-g (a.q i))| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ = |∑ i, a.coeff i*((f (a.p i)-g (a.p i))-(f (a.q i)-g (a.q i)))| := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, |a.coeff i*((f (a.p i)-g (a.p i))-(f (a.q i)-g (a.q i)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a.coeff i| * (2*δ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [hp i,hq i])) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem finite_smooth_pair_approx {N : ℕ} (a : Fin N → MolecularData H)
    (f : H → ℝ) (hf : LipschitzWith 1 f) (hf0 : f 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Smooth H, LipschitzWith 1 g.val ∧ g.val 0 = 0 ∧
      ∀ i, |smoothPair (a i) g-molPair (a i) f| < ε := by
  classical
  let B : ℝ := ∑ i, ∑ j, |(a i).coeff j|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  let δ : ℝ := ε/(4*(B+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  let S : Finset H := {0} ∪ Finset.univ.biUnion (fun i : Fin N =>
    (Finset.univ.image (a i).p) ∪ (Finset.univ.image (a i).q))
  have hS : (0:H) ∈ S := by simp [S]
  obtain ⟨g,hg,hgLip,hg0,hclose⟩ := exists_smooth_finite_approx S hS f hf0
    (fun p _ q _ => by simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hf.dist_le_mul p q) hδ
  refine ⟨⟨g,hg⟩,hgLip,hg0,fun i => ?_⟩
  have hp (j : Fin (a i).n) : (a i).p j ∈ S := by simp only [S,Finset.mem_union,Finset.mem_singleton,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]; exact Or.inr ⟨i,Or.inl ⟨j,rfl⟩⟩
  have hq (j : Fin (a i).n) : (a i).q j ∈ S := by simp only [S,Finset.mem_union,Finset.mem_singleton,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]; exact Or.inr ⟨i,Or.inr ⟨j,rfl⟩⟩
  have hi : (∑ j, |(a i).coeff j|) ≤ B :=
    Finset.single_le_sum (f := fun j : Fin N => ∑ k, |(a j).coeff k|) (fun j _ => Finset.sum_nonneg (fun k _ => abs_nonneg _)) (Finset.mem_univ i)
  have hb : 2*δ*B < ε := by
    have he : δ*(4*(B+1)) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  exact (molPair_approx (a i) g f (fun j => (hclose _ (hp j)).le)
    (fun j => (hclose _ (hq j)).le)).trans_lt
      ((mul_le_mul_of_nonneg_left hi (by positivity)).trans_lt hb)

theorem triangularRows_rich {K : Set H} (h0 : (0:H) ∈ K)
    (u : ℕ → supported K) (φ : ((supported K) →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hφ : ∀ f, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f)))
    {d C ρ α : ℝ} (hd : 0 < d) (hC : 0 < C) (hρ : 0 < ρ) (hα : 0 < α)
    (hρα : ρ ≤ α/4) (hαd : 32*α ≤ d) (hu : ∀ n, ‖u n‖ ≤ C)
    (hfar : ∀ x : supported K, d ≤ @norm (((supported K) →L[ℝ] ℝ) →L[ℝ] ℝ) inferInstance (φ-NormedSpace.inclusionInDoubleDual ℝ (supported K) x)) :
    (triangularRows K C ρ α (fun n => (u n : Space H))).Rich := by
  classical
  intro N
  obtain ⟨f,v,hf,hhigh,hlow⟩ := WeakSequences.exists_triangular_duals hφ hd hfar N
  have hext (j : Fin N) : ∃ T : Space H →L[ℝ] ℝ,
      (∀ x : supported K, T x = f j x) ∧ ‖T‖ = 1 := by
    obtain ⟨T,hT,hTnorm⟩ := exists_extension_norm_eq (supported K) (f j)
    exact ⟨T,hT,hTnorm.trans (hf j).1⟩
  choose T hT hTnorm using hext
  have happ (i : Fin N) := exists_molecular_approx h0 (u (v i)).val (u (v i)).property hC (hu (v i)) hρ
  choose a haK haC haclose using happ
  have hLip (j : Fin N) : LipschitzWith 1 (fun p => T j (point p)) := by
    convert dual_point_lipschitz (T j) using 1
    apply NNReal.coe_injective
    simpa using (hTnorm j).symm
  have hsm (j : Fin N) := finite_smooth_pair_approx a (fun p => T j (point p)) (hLip j)
    (by simp) (show 0 < α/4 by positivity)
  choose g hgLip hg0 hgclose using hsm
  let row : Fin N → RowItem K C ρ (fun n => (u n : Space H)) := fun j =>
    ⟨g j,hgLip j,hg0 j,a j,haK j,haC j,⟨v j,haclose j⟩⟩
  have hpair (i j : Fin N) : |molPair (a i) (fun p => T j (point p))-f j (u (v i))| < ρ := by
    rw [← dual_molecular,← hT j,← map_sub,← Real.norm_eq_abs]
    have hn := (T j).le_opNorm ((a i).vector-(u (v i) : Space H))
    rw [hTnorm j,one_mul,norm_sub_rev] at hn
    exact hn.trans_lt (haclose i)
  refine ⟨row,?_,?_⟩
  · intro i j hij
    have hg' := hgclose j i
    have hp' := hpair i j
    have hh := hhigh i j hij
    change 4*α ≤ smoothPair (a i) (g j)
    rw [abs_lt] at hg' hp'
    linarith
  · intro i j hij
    have hg' := hgclose j i
    have hp' := hpair i j
    rw [hlow i j hij,sub_zero] at hp'
    change |smoothPair (a i) (g j)| ≤ α
    have he := abs_add_le (smoothPair (a i) (g j)-molPair (a i) (fun p => T j (point p)))
      (molPair (a i) (fun p => T j (point p)))
    rw [sub_add_cancel] at he
    linarith

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSpace
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSpace
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSubtypeSpaceMemSubmoduleRealSupported
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSubtypeSpaceMemSubmoduleSupported
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeSpaceMemSubmoduleSupported
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealContinuousLinearMapIdSubtypeSpaceMemSubmoduleSupported


theorem solution.{uH} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.triangularRows_rich.{uH} := @_root_.OAI.LipschitzCounterexample.CompactWSC.triangularRows_rich.{uH}
