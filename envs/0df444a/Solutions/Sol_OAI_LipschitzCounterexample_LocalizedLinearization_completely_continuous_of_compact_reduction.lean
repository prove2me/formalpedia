-- Prove2me | solution 1 for OAI.LipschitzCounterexample.LocalizedLinearization.completely_continuous_of_compact_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:38:06.653833+00:00
-- url     : https://prove2.me/submissions/89cdf754-bd03-4da6-a37e-e896fa5a0e06

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CompleteContinuity.lean:L98-L169
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.LocalizedLinearization.completely_continuous_of_compact_reduction. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_linearize_unique
import Theorems.Thm_OAI_LipschitzCounterexample_LocalGeometry_badSet_finite
import Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_scalar_localization

-- ---- from OAI.Analysis.LipschitzEquivalence.Schur ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF

noncomputable section
namespace LipschitzCounterexample

namespace WeakSequences
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem WeakNull.map {u : ℕ → E} (hu : WeakNull u) (T : E →L[ℝ] F) :
    WeakNull (fun n => T (u n)) := fun f => hu (f.comp T)

theorem WeakNull.subseq {u : ℕ → E} (hu : WeakNull u) {a : ℕ → ℕ} (ha : StrictMono a) :
    WeakNull (fun n => u (a n)) := fun f => (hu f).comp ha.tendsto_atTop

end WeakSequences

end LipschitzCounterexample
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.LocalLipschitz ----
namespace OAI

universe uM uN uB uIndex

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {N : Type uN} [MetricSpace M] [MetricSpace N]

theorem quotients_nonempty (f : M → N) (S : Set M) : (quotients f S).Nonempty :=
  ⟨0,Or.inl rfl⟩

theorem constant_le {f : M → N} {S : Set M} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) : constant f S ≤ L := by
  apply csSup_le (quotients_nonempty f S)
  rintro r (rfl | ⟨x,hx,y,hy,rfl⟩)
  · exact L.coe_nonneg
  · exact quotient_le hf hx hy

theorem lipschitzOn_constant {f : M → N} {S : Set M} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) : LipschitzOnWith ⟨constant f S,constant_nonneg hf⟩ f S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hxy : x = y
  · simp [hxy]
  · have hq : dist (f x) (f y) / dist x y ≤ constant f S :=
      le_csSup (quotients_bounded hf) (Or.inr ⟨x,hx,y,hy,rfl⟩)
    exact (div_le_iff₀ (dist_pos.mpr hxy)).mp hq

theorem subsequence_constants {B : Type uB} [Countable B] (O : B → Set M)
    (f : ℕ → M → N) {L : ℝ≥0} (hf : ∀ i, LipschitzWith L (f i)) :
    ∃ a : B → ℝ, ∃ s : ℕ → ℕ, StrictMono s ∧
      (∀ b, a b ∈ Icc (0 : ℝ) L) ∧
      ∀ b, Tendsto (fun i => constant (f (s i)) (O b)) atTop (𝓝 (a b)) := by
  let v : ℕ → B → Icc (0 : ℝ) L := fun i b =>
    ⟨constant (f i) (O b), constant_nonneg (hf i).lipschitzOnWith,
      constant_le (hf i).lipschitzOnWith⟩
  obtain ⟨a,s,hs,ha⟩ := CompactSpace.tendsto_subseq v
  refine ⟨fun b => a b,s,hs,fun b => (a b).property,?_⟩
  intro b
  exact (continuous_subtype_val.tendsto _).comp
    ((continuous_apply b).tendsto a |>.comp ha)

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} [MetricSpace M]

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalGeometry
open CoordinateSpaces LocalLipschitz
variable {M : Type uM} [MetricSpace M] {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

end LipschitzCounterexample.LocalGeometry
namespace LipschitzCounterexample.LocalGeometry
open CoordinateSpaces LocalLipschitz
variable {M : Type uM} [MetricSpace M] {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

end LipschitzCounterexample.LocalGeometry

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.CompleteContinuity ----
namespace OAI

universe uE uM uIndex

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.WeakSequences
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [NormedSpace ℝ E] in
theorem exists_large_subsequence (u : ℕ → E) (hu : ¬ Tendsto u atTop (𝓝 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ i, ε ≤ ‖u (s i)‖ := by
  rw [Metric.tendsto_atTop] at hu
  push Not at hu
  obtain ⟨ε,hε,hlarge⟩ := hu
  simp only [dist_zero_right] at hlarge
  have hstep (p : ℕ) : ∃ n : ℕ, p < n ∧ ε ≤ ‖u n‖ := by
    obtain ⟨n,hn,hun⟩ := hlarge (p+1)
    exact ⟨n,lt_of_lt_of_le (Nat.lt_succ_self p) hn,hun⟩
  let next (p : ℕ) : ℕ := Classical.choose (hstep p)
  let seq : ℕ → ℕ := fun j => Nat.rec 0 (fun _ p => next p) j
  have hseq (j : ℕ) : seq j < seq (j+1) ∧ ε ≤ ‖u (seq (j+1))‖ :=
    Classical.choose_spec (hstep (seq j))
  have hm : StrictMono seq := strictMono_nat_of_lt_succ (fun j => (hseq j).1)
  exact ⟨ε,hε,(fun i => seq (i+1)),(fun _ _ h => hm (Nat.add_lt_add_right h 1)),fun i => (hseq i).2⟩

theorem norm_unitNormalize (u : ℕ → E) {ε : ℝ} (hε : 0 < ε)
    (hu : ∀ i, ε ≤ ‖u i‖) (i : ℕ) : ‖unitNormalize u i‖ = 1 := by
  have hn : ‖u i‖ ≠ 0 := ne_of_gt (hε.trans_le (hu i))
  simp [unitNormalize,norm_smul,hn]

theorem WeakNull.unitNormalize {u : ℕ → E} (hw : WeakNull u) {ε : ℝ} (hε : 0 < ε)
    (hu : ∀ i, ε ≤ ‖u i‖) : WeakNull (unitNormalize u) := by
  intro f
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hw f) (δ*ε) (mul_pos hδ hε)
  refine ⟨N,fun i hi => ?_⟩
  have hn : 0 < ‖u i‖ := hε.trans_le (hu i)
  have hfi := hN i hi
  simp only [dist_zero_right,Real.norm_eq_abs] at hfi ⊢
  change |f (‖u i‖⁻¹ • u i)| < δ
  rw [map_smul,smul_eq_mul,abs_mul,abs_inv,abs_norm]
  rw [← div_eq_inv_mul]
  apply (div_lt_iff₀ hn).mpr
  exact hfi.trans_le (mul_le_mul_of_nonneg_left (hu i) hδ.le)
end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz CoordinateSpaces LocalGeometry
open scoped NNReal InnerProductSpace
variable {M : Type uM} [MetricSpace M] [Zero M]
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

theorem scalar_test_pairing (D : M → Hilbert (ι := ι)) {L : ℝ≥0}
    (hD : LipschitzWith L D) (hD0 : D 0 = 0) (b : Hilbert (ι := ι)) (hb : ‖b‖ ≤ 1)
    (μ : FreeSpace.Space M) :
    test (normalized (fun x => ⟪D x,b⟫_ℝ) (scalar_test_lipschitz D hD b hb)) μ =
      ⟪FreeSpace.linearize D μ,b⟫_ℝ := by
  let d : M → ℝ := fun x => ⟪D x,b⟫_ℝ
  have hd : LipschitzWith L d := scalar_test_lipschitz D hD b hb
  have hd0 : d 0 = 0 := by simp [d,hD0]
  have h₁ : FreeSpace.linearize d = test (normalized d hd) :=
    FreeSpace.linearize_unique d hd hd0 _ (by
      intro x
      change d x-d 0 = d x
      rw [hd0,sub_zero])
  have h₂ : FreeSpace.linearize d = (innerSL ℝ b).comp (FreeSpace.linearize D) :=
    FreeSpace.linearize_unique d hd hd0 _ (by
      intro x
      rw [ContinuousLinearMap.comp_apply,FreeSpace.linearize_point D hD hD0]
      exact (real_inner_comm b (D x)).symm)
  have he := congrArg (fun T : FreeSpace.Space M →L[ℝ] ℝ => T μ) (h₁.symm.trans h₂)
  change test (normalized d hd) μ = ⟪FreeSpace.linearize D μ,b⟫_ℝ
  rw [he]
  exact (real_inner_comm b (FreeSpace.linearize D μ)).symm

theorem completely_continuous_of_compact_reduction [SecondCountableTopology M]
    (hcompact : FreeSpace.HasCompactReduction (M := M))
    (D : M → Hilbert (ι := ι)) {L : ℝ≥0} (hD : LipschitzWith L D) (hD0 : D 0 = 0)
    (hloc : LocalOrthogonality D) : WeakSequences.CompletelyContinuous (FreeSpace.linearize D) := by
  classical
  intro μ hw
  by_contra hn
  obtain ⟨ε,hε,s,hs,hlarge⟩ := WeakSequences.exists_large_subsequence
    (fun i => FreeSpace.linearize D (μ i)) hn
  let μ' : ℕ → FreeSpace.Space M := fun i => μ (s i)
  have hw' : WeakSequences.WeakNull μ' := hw.subseq hs
  let b := WeakSequences.unitNormalize (fun i => FreeSpace.linearize D (μ' i))
  have hwq : WeakSequences.WeakNull (fun i => FreeSpace.linearize D (μ' i)) := hw'.map _
  have hbn (i : ℕ) : ‖b i‖ = 1 := WeakSequences.norm_unitNormalize _ hε hlarge i
  have hbw : WeakSequences.WeakNull b := hwq.unitNormalize hε hlarge
  let d : ℕ → M → ℝ := fun i x => ⟪D x,b i⟫_ℝ
  have hd (i : ℕ) : LipschitzWith L (d i) := scalar_test_lipschitz D hD (b i) (hbn i).le
  have hpoint (x : M) : Tendsto (fun i => d i x) atTop (𝓝 0) := hbw (innerSL ℝ (D x))
  have hpair (i : ℕ) : test (normalized (d i) (hd i)) (μ' i) = ‖FreeSpace.linearize D (μ' i)‖ := by
    rw [scalar_test_pairing D hD hD0 (b i) (hbn i).le]
    change ⟪FreeSpace.linearize D (μ' i),‖FreeSpace.linearize D (μ' i)‖⁻¹ • FreeSpace.linearize D (μ' i)⟫_ℝ = _
    rw [inner_smul_right,real_inner_self_eq_norm_sq]
    have hn' : ‖FreeSpace.linearize D (μ' i)‖ ≠ 0 := ne_of_gt (hε.trans_le (hlarge i))
    field_simp
  by_cases hL : L = 0
  · have hdzero (i : ℕ) : d i = 0 := by
      funext x
      have ht := (hd i).dist_le_mul x 0
      simp only [hL,NNReal.coe_zero,zero_mul,dist_le_zero] at ht
      simpa [d,hD0] using ht
    have htest : test (normalized (d 0) (hd 0)) (μ' 0) = 0 := by
      change (μ' 0).1 _ = 0
      have ht : normalized (d 0) (hd 0) = 0 := by
        apply Subtype.ext
        funext x
        change d 0 x-d 0 0 = 0
        rw [hdzero]
        simp
      rw [ht,map_zero]
    rw [hpair] at htest
    linarith [hlarge 0]
  have hLpos : 0 < L := lt_of_le_of_ne (by positivity) (Ne.symm hL)
  obtain ⟨B,hBc,hBne,hB⟩ := TopologicalSpace.exists_countable_basis M
  let O : B → Set M := Subtype.val
  let : Countable B := hBc.to_subtype
  obtain ⟨a,t,ht,ha,halim⟩ := subsequence_constants O d hd
  have hbase : ∀ z : M, ∀ r : ℝ, 0 < r → ∃ j, z ∈ O j ∧ O j ⊆ Metric.ball z r := by
    intro z r hr
    obtain ⟨P,hPB,hzP,hPball⟩ := hB.exists_subset_of_mem_open (Metric.mem_ball_self hr) Metric.isOpen_ball
    exact ⟨⟨P,hPB⟩,hzP,hPball⟩
  have hbad (η : ℝ≥0) (hη : 0 < η) : (badSet O a (η : ℝ)).Finite :=
    badSet_finite D hLpos hD hloc (fun i => b (t i)) (fun i => (hbn _).le)
      (fun a => (hbw (coord a)).comp ht.tendsto_atTop) O hbase a halim hη
  have hgood : ∀ η : ℝ≥0, 0 < η → ∃ Z : Set M, Z.Finite ∧
      ∀ p, p ∉ Z → ∃ P : Set M, IsOpen P ∧ p ∈ P ∧
        ∀ᶠ i in atTop, LipschitzOnWith η (d (t i)) P := by
    intro η hη
    refine ⟨badSet O a (η : ℝ),hbad η hη,?_⟩
    intro p hp
    change ¬ (∀ j, p ∈ O j → (η : ℝ) ≤ a j) at hp
    push Not at hp
    obtain ⟨j,hpj,haj⟩ := hp
    refine ⟨O j,hB.isOpen j.property,hpj,?_⟩
    have he := (halim j).eventually (eventually_lt_nhds haj)
    filter_upwards [he] with i hi
    exact (lipschitzOn_constant (hd (t i)).lipschitzOnWith).weaken hi.le
  have hvanish := scalar_localization hcompact (hw'.subseq ht) (fun i => d (t i))
    (fun i => hd (t i)) (fun x => (hpoint x).comp ht.tendsto_atTop) hgood
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hvanish ε hε
  have hcontra := hN N le_rfl
  rw [dist_zero_right,Real.norm_eq_abs,hpair,abs_of_nonneg (norm_nonneg _)] at hcontra
  exact (not_lt_of_ge (hlarge (t N))) hcontra
end LipschitzCounterexample.LocalizedLinearization

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalizedLinearization
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open Filter Set Topology LocalLipschitz CoordinateSpaces LocalGeometry
open scoped NNReal InnerProductSpace


theorem solution.{uM,uIndex} : type_of% @_root_.OAI.LipschitzCounterexample.LocalizedLinearization.completely_continuous_of_compact_reduction.{uM,uIndex} := @_root_.OAI.LipschitzCounterexample.LocalizedLinearization.completely_continuous_of_compact_reduction.{uM,uIndex}
