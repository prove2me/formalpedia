-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.exists_scaled_slice_rearrangement_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:18.799222+00:00
-- url     : https://prove2.me/submissions/54aa20a6-73c5-48e9-bdaf-fc50308c628f

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_hamiltonian_rounded_intervals_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ParametricMoser
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory

theorem radiusSq_smul (a : ℝ) (p : Plane) : radiusSq (a • p) = a^2*radiusSq p := by
  change (a*p.1)^2+(a*p.2)^2 = a^2*(p.1^2+p.2^2)
  ring

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology ENNReal
open Set Function MeasureTheory
open Filter
open scoped Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,E) hK.isClosed hKL (n := ⊤)
  have hs : tsupport (χ : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  exact ⟨χ,χ.contMDiff.contDiff,hL.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hLU,hχ1,hχrange⟩

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_FlatIsotopy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
open scoped ComplexConjugate
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SupportedSmoothIsotopy

 theorem mapsTo {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) :
    MapsTo (Φ.map t) W W := by
  intro x hx
  by_contra hn
  have hn' : Φ.map t x ∉ Φ.support := fun h => hn (Φ.support_subset h)
  have he := Φ.fixed t (Φ.map t x) hn'
  exact hn (((Φ.map t).injective he).symm ▸ hx)

end SupportedSmoothIsotopy

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_SmoothConvexSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology Manifold
open Set Function
variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_convex_selection {Y : Set P} (hY : IsClosed Y)
    (S : P → Set F) (hopen : ∀ v, IsOpen {y | v ∈ S y})
    (hconv : ∀ y ∈ Y, Convex ℝ (S y)) (hne : ∀ y ∈ Y, (S y).Nonempty) :
    ∃ c : P → F, ContDiff ℝ ∞ c ∧ ∀ y ∈ Y, c y ∈ S y := by
  classical
  choose v hv using fun y : Y => hne y y.property
  let U : Y → Set P := fun y => {x | v y ∈ S x}
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,P) hY U
    (fun y => hopen (v y)) (by
      intro y hy
      exact mem_iUnion_of_mem ⟨y,hy⟩ (hv ⟨y,hy⟩))
  refine ⟨fun y => ∑ᶠ i, ρ i y • v i,?_,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro y
    exact ρ.contDiffAt_finsum (fun _ _ => contDiffAt_const)
  · intro y hy
    apply ρ.finsum_smul_mem_convex hy _ (hconv y hy)
    intro i hi
    exact hρ i (subset_tsupport (ρ i) hi)


end

section
open Set Function

theorem exists_strict_interval_extension {a b l u L : ℝ}
    (hal : a < l) (hub : u < b) (hLu : u-l < L) (hLb : L < b-a) :
    ∃ c, a < c ∧ c+L < b ∧ c < l ∧ u < c+L := by
  have hh : max a (u-L) < min l (b-L) := by
    rw [max_lt_iff,lt_min_iff,lt_min_iff]
    constructor <;> constructor <;> linarith
  obtain ⟨c,hlo,hhi⟩ := exists_between hh
  exact ⟨c,(le_max_left _ _).trans_lt hlo,
    by linarith [(lt_of_lt_of_le hhi (min_le_right _ _))],
    hhi.trans_le (min_le_left _ _),
    by linarith [(lt_of_le_of_lt (le_max_right _ _) hlo)]⟩

theorem exists_strict_nested_intervals {n : ℕ} (a b L : Fin n → ℝ)
    (ha : Antitone a) (hb : Monotone b) (hL : StrictMono L)
    (hfit : ∀ i, L i < b i-a i) :
    ∃ c : Fin n → ℝ, (∀ i, a i < c i ∧ c i+L i < b i) ∧
      ∀ ⦃i j⦄, i < j → c j < c i ∧ c i+L i < c j+L j := by
  induction n with
  | zero => exact ⟨fun i => i.elim0,by simp,by simp⟩
  | succ n ih =>
    cases n with
    | zero =>
      refine ⟨fun i => (a i+b i-L i)/2,?_,?_⟩
      · intro i; have := hfit i; constructor <;> linarith
      · intro i j hij
        have : i = j := by omega
        exact (lt_irrefl _ (this ▸ hij)).elim
    | succ m =>
      obtain ⟨c,hc,hnest⟩ := ih (a ∘ Fin.castSucc) (b ∘ Fin.castSucc)
        (L ∘ Fin.castSucc) (ha.comp_monotone Fin.strictMono_castSucc.monotone)
        (hb.comp Fin.strictMono_castSucc.monotone) (hL.comp Fin.strictMono_castSucc)
        (fun i => hfit i.castSucc)
      let i₀ : Fin (m+1) := Fin.last m
      let j₀ : Fin (m+2) := Fin.last (m+1)
      have hij : i₀.castSucc < j₀ := Fin.castSucc_lt_last _
      obtain ⟨d,hd⟩ := exists_strict_interval_extension
        ((ha hij.le).trans_lt (hc i₀).1)
        ((hc i₀).2.trans_le (hb hij.le))
        (by simpa only [Function.comp_apply,add_sub_cancel_left] using hL hij)
        (hfit j₀)
      refine ⟨Fin.snoc c d,?_,?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using And.intro hd.1 hd.2.1
        · simpa only [Fin.snoc_castSucc,Function.comp_apply] using hc j
      · intro i j hij'
        have hi : i ≠ Fin.last (m+1) := by
          intro hh
          subst i
          exact not_lt_of_ge (Fin.le_last _) hij'
        obtain ⟨i,rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        revert hij'
        refine Fin.lastCases ?_ (fun j hj => ?_) j
        · intro _
          simp only [Fin.snoc_castSucc,Fin.snoc_last]
          rcases lt_or_eq_of_le (Fin.le_last i) with hi | hi
          · have hh := hnest hi
            exact ⟨hd.2.2.1.trans hh.1,hh.2.trans hd.2.2.2⟩
          · subst i
            exact hd.2.2
        · simpa only [Fin.snoc_castSucc,Function.comp_apply] using
            hnest (show i < j from hj)


end

section
open scoped ContDiff Topology
open Set Function

variable {n : ℕ}

theorem intervalPlacements_convex (L : Fin n → ℝ) (V : Fin n → Set ℝ)
    (hV : ∀ i, Convex ℝ (V i)) : Convex ℝ (IntervalPlacements L V) := by
  intro c hc d hd α β hα hβ hab
  refine ⟨?_,?_⟩
  · intro i
    have he : (α • c+β • d) i+L i = α*(c i+L i)+β*(d i+L i) := by
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      have he := congrArg (fun t : ℝ => t*L i) hab
      nlinarith only [he]
    constructor
    · exact hV i (hc.1 i).1 (hd.1 i).1 hα hβ hab
    · rw [he]
      exact hV i (hc.1 i).2 (hd.1 i).2 hα hβ hab
  · intro i j hij
    let A : (Fin n → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj i
    let B : (Fin n → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
    have ha : A c < 0 := sub_neg.mpr (hc.2 hij).1
    have hb : A d < 0 := sub_neg.mpr (hd.2 hij).1
    have ha' : B c < L j-L i := by change c i-c j < _; linarith [(hc.2 hij).2]
    have hb' : B d < L j-L i := by change d i-d j < _; linarith [(hd.2 hij).2]
    have hh := (convex_halfSpace_lt A.isLinear 0) ha hb hα hβ hab
    have hh' := (convex_halfSpace_lt B.isLinear (L j-L i)) ha' hb' hα hβ hab
    change (α • c+β • d) j-(α • c+β • d) i < 0 at hh
    change (α • c+β • d) i-(α • c+β • d) j < L j-L i at hh'
    exact ⟨sub_neg.mp hh,by linarith⟩

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_smooth_nested_intervals {Y : Set P} (hY : IsClosed Y)
    (L : Fin n → ℝ) (hL : StrictMono L) (V : P → Fin n → Set ℝ)
    (hopen : ∀ i t, IsOpen {y | t ∈ V y i})
    (hconv : ∀ y ∈ Y, ∀ i, Convex ℝ (V y i))
    (hroom : ∀ y ∈ Y, ∃ a b : Fin n → ℝ, Antitone a ∧ Monotone b ∧
      (∀ i, L i < b i-a i) ∧ ∀ i, Ioo (a i) (b i) ⊆ V y i)
    (hpos : ∀ i, 0 < L i) :
    ∃ c : P → (Fin n → ℝ), ContDiff ℝ ∞ c ∧
      ∀ y ∈ Y, (∀ i, Icc (c y i) (c y i+L i) ⊆ V y i) ∧
        StrictNestedStarts L (c y) := by
  have hsopen (c : Fin n → ℝ) : IsOpen {y | c ∈ IntervalPlacements L (V y)} := by
    change IsOpen {y | (∀ i, c i ∈ V y i ∧ c i+L i ∈ V y i) ∧ StrictNestedStarts L c}
    by_cases hn : StrictNestedStarts L c
    · simp only [hn,and_true,ofPred_forall,ofPred_and]
      exact isOpen_iInter_of_finite (fun i => (hopen i (c i)).inter (hopen i (c i+L i)))
    · simp only [hn,and_false,ofPred_false,isOpen_empty]
  have hsne (y : P) (hy : y ∈ Y) : (IntervalPlacements L (V y)).Nonempty := by
    obtain ⟨a,b,ha,hb,hfit,hsub⟩ := hroom y hy
    obtain ⟨c,hc,hn⟩ := exists_strict_nested_intervals a b L ha hb hL hfit
    refine ⟨c,?_,hn⟩
    intro i
    have hLi := hpos i
    exact ⟨hsub i ⟨(hc i).1,by linarith [(hc i).2]⟩,
      hsub i ⟨by linarith [(hc i).1],(hc i).2⟩⟩
  obtain ⟨c,hc,hmem⟩ := exists_smooth_convex_selection hY
    (fun y => IntervalPlacements L (V y)) hsopen
    (fun y hy => intervalPlacements_convex L (V y) (hconv y hy)) hsne
  refine ⟨c,hc,?_⟩
  intro y hy
  refine ⟨?_,(hmem y hy).2⟩
  intro i
  exact (hconv y hy i).ordConnected.out ((hmem y hy).1 i).1 ((hmem y hy).1 i).2


end

open scoped ContDiff Topology
open Set Function MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CompactEmbeddingIsotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory

theorem areaRadius_sq {a : ℝ} (ha : 0 ≤ a) : (areaRadius a)^2 = a/Real.pi :=
  Real.sq_sqrt (div_nonneg ha Real.pi_pos.le)

theorem mem_closedRoundDisk_areaRadius {a : ℝ} (ha : 0 ≤ a) (x : Plane) :
    x ∈ closedRoundDisk (areaRadius a) ↔ radialArea x ≤ a := by
  change radiusSq x ≤ (areaRadius a)^2 ↔ Real.pi * radiusSq x ≤ a
  rw [areaRadius_sq ha,le_div_iff₀ Real.pi_pos,mul_comm]

theorem mem_roundDisk_areaRadius {a : ℝ} (ha : 0 ≤ a) (x : Plane) :
    x ∈ roundDisk (areaRadius a) ↔ radialArea x < a := by
  change radiusSq x < (areaRadius a)^2 ↔ Real.pi * radiusSq x < a
  rw [areaRadius_sq ha,lt_div_iff₀ Real.pi_pos,mul_comm]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RearrangementBounds
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

namespace HamiltonianDiskIsotopyFamily

theorem mapsTo_closed {R : ℝ} (Ψ : HamiltonianDiskIsotopyFamily P R) (y : P) (t : ℝ) :
    MapsTo (Ψ.isotopy.map y t) (closedRoundDisk R) (closedRoundDisk R) := by
  intro x hx
  by_cases hi : x ∈ roundDisk R
  · have hm := (Ψ.isotopy.eval y).mapsTo t hi
    change radiusSq (Ψ.isotopy.map y t x) < R^2 at hm
    exact hm.le
  · rw [Ψ.isotopy.fixed y t x (fun hs => hi (Ψ.isotopy.support_subset hs))]
    exact hx

end HamiltonianDiskIsotopyFamily

theorem radialArea_nonneg (x : Plane) : 0 ≤ radialArea x :=
  mul_nonneg Real.pi_pos.le (by dsimp [radiusSq] <;> positivity)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem planeMoments_nonneg (z : PlanePhase ι) (i : ι) : 0 ≤ planeMoments z i :=
  radialArea_nonneg (z i)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_ScaledPlanarMotion
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

@[simp] theorem radialArea_smul (a : ℝ) (x : Plane) :
    radialArea (a • x) = a^2*radialArea x := by
  simp only [radialArea,radiusSq_smul]
  ring

theorem scaledPlanarTrace_cutoff_zero (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (hχ : χ y = 0) (t : ℝ) (x : Plane) :
    scaledPlanarTrace Ψ a χ y t x = x := by
  simp only [scaledPlanarTrace,hχ,zero_mul,Ψ.zero]
  exact smul_inv_smul₀ ha x

theorem scaledPlanarTrace_time_one (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (y : P) (hχ : χ y = 1) (x : Plane) :
    scaledPlanarTrace Ψ a χ y 1 x = a y • Ψ.trace y 1 ((a y)⁻¹ • x) := by
  simp [scaledPlanarTrace,hχ,Real.smoothTransition.one_of_one_le le_rfl]

theorem scaled_disk_fixed (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1))
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (t : ℝ) (x : Plane)
    (hx : (a y)^2 ≤ radialArea x) : scaledPlanarTrace Ψ.motion a χ y t x = x := by
  have hs : (a y)⁻¹ • x ∉ roundDisk (areaRadius 1) := by
    rw [mem_roundDisk_areaRadius (by norm_num),radialArea_smul,not_lt]
    have hh := mul_le_mul_of_nonneg_left hx (sq_nonneg (a y)⁻¹)
    have he : (a y)⁻¹^2*(a y)^2 = 1 := by field_simp
    linarith
  dsimp only [scaledPlanarTrace,HamiltonianDiskIsotopyFamily.motion]
  rw [Ψ.isotopy.fixed y _ _ (fun h => hs (Ψ.isotopy.support_subset h))]
  exact smul_inv_smul₀ ha x

theorem scaled_disk_mapsTo (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1))
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (t : ℝ) (x : Plane)
    (hx : radialArea x ≤ (a y)^2) :
    radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ (a y)^2 := by
  have hs : (a y)⁻¹ • x ∈ closedRoundDisk (areaRadius 1) := by
    rw [mem_closedRoundDisk_areaRadius (by norm_num),radialArea_smul]
    have hh := mul_le_mul_of_nonneg_left hx (sq_nonneg (a y)⁻¹)
    have he : (a y)⁻¹^2*(a y)^2 = 1 := by field_simp
    linarith
  have hm := Ψ.mapsTo_closed y (χ y*Real.smoothTransition t) hs
  rw [mem_closedRoundDisk_areaRadius (by norm_num)] at hm
  dsimp only [scaledPlanarTrace,HamiltonianDiskIsotopyFamily.motion]
  rw [radialArea_smul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (sq_nonneg (a y))

theorem scaled_disk_preserves_slice (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1))
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (t : ℝ) (x : Plane) {L : ℝ}
    (hx : radialArea x ≤ L) (hfit : χ y ≠ 0 → (a y)^2 ≤ L) :
    radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ L := by
  by_cases hc : χ y = 0
  · rw [scaledPlanarTrace_cutoff_zero Ψ.motion y ha hc]; exact hx
  · rcases le_total (radialArea x) ((a y)^2) with hl | hl
    · exact (scaled_disk_mapsTo Ψ y ha t x hl).trans (hfit hc)
    · rw [scaled_disk_fixed Ψ y ha t x hl]; exact hx

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Comparison
open scoped Topology
open Set Function Filter
section

theorem exists_longer_strict_interval {f : ℝ → ℝ} (hf : Continuous f)
    {a h c : ℝ} (ha : 0 ≤ a) (hah : a+h ≤ 1) (_hh : 0 ≤ h) (hh1 : h < 1)
    (hla : f a < c) (hlb : f (a+h) < c) :
    ∃ u v : ℝ, 0 < u ∧ v < 1 ∧ h < v-u ∧ f u < c ∧ f v < c := by
  let u₀ : ℝ := (1-h)/4
  let v₀ : ℝ := (3+h)/4
  have hu₀ : 0 < u₀ := by dsimp [u₀] <;> linarith
  have hv₀ : v₀ < 1 := by dsimp [v₀] <;> linarith
  have huv₀ : h < v₀-u₀ := by dsimp [u₀,v₀] <;> linarith
  let u (t : ℝ) := (1-t)*a+t*u₀
  let v (t : ℝ) := (1-t)*(a+h)+t*v₀
  have huc : Continuous u := by dsimp [u]; fun_prop
  have hvc : Continuous v := by dsimp [v]; fun_prop
  have heu : ∀ᶠ t : ℝ in 𝓝 0, f (u t) < c :=
    (hf.comp huc).continuousAt.tendsto.eventually (isOpen_Iio.mem_nhds (by simpa [u] using hla))
  have hev : ∀ᶠ t : ℝ in 𝓝 0, f (v t) < c :=
    (hf.comp hvc).continuousAt.tendsto.eventually (isOpen_Iio.mem_nhds (by simpa [v] using hlb))
  have he : ∀ᶠ t : ℝ in 𝓝 0, t < 1 ∧ f (u t) < c ∧ f (v t) < c := by
    filter_upwards [(isOpen_Iio.mem_nhds (by norm_num : (0:ℝ) ∈ Iio 1) : Iio (1:ℝ) ∈ 𝓝 (0:ℝ)),heu,hev] with t ht hu hv
    exact ⟨ht,hu,hv⟩
  obtain ⟨t,ht,htpos⟩ := ((he.filter_mono
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).and self_mem_nhdsWithin).exists
  refine ⟨u t,v t,?_,?_,?_,ht.2.1,ht.2.2⟩
  · dsimp [u]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [ht.1]) ha) (mul_pos htpos hu₀)
  · dsimp [v]
    nlinarith only [mul_nonneg (by linarith [ht.1] : 0 ≤ 1-t) (sub_nonneg.mpr hah),
      mul_pos htpos (sub_pos.mpr hv₀)]
  · dsimp [u,v]
    nlinarith only [mul_pos htpos (sub_pos.mpr huv₀)]

variable {P : Type*} [TopologicalSpace P] {m : ℕ}

theorem intervalRoom_open (V : P → Fin m → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i}) :
    IsOpen {p : (Fin m → ℝ) × P | IntervalRoom V p.1 p.2} := by
  have hmem (i : Fin m) (a : ℝ) : IsOpen {p : (Fin m → ℝ) × P | a ∈ V p.2 i} :=
    (hV i).preimage (continuous_snd.prodMk continuous_const)
  change IsOpen {p : (Fin m → ℝ) × P | ∀ i, ∃ a b : ℝ,
    a ∈ V p.2 i ∧ b ∈ V p.2 i ∧ p.1 i < b-a}
  simp only [ofPred_forall,ofPred_exists,ofPred_and]
  exact isOpen_iInter_of_finite (fun i => isOpen_iUnion (fun a => isOpen_iUnion (fun b =>
    (hmem i a).inter ((hmem i b).inter (isOpen_lt ((continuous_apply i).comp continuous_fst) continuous_const)))))

theorem strictMono_open : IsOpen {L : Fin m → ℝ | StrictMono L} := by
  change IsOpen {L : Fin m → ℝ | ∀ i j, i < j → L i < L j}
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i < j
  · simpa [hij] using isOpen_lt (f := fun u : Fin m → ℝ => u i) (g := fun u => u j)
      (continuous_apply i) (continuous_apply j)
  · simp [hij]

theorem exists_uniform_interval_widths {Y : Set P} (hY : IsCompact Y)
    (h : Fin m → ℝ) (hh : StrictMono h) (V : P → Fin m → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i})
    (hroom : ∀ y ∈ Y, IntervalRoom V h y) :
    ∃ L w : Fin m → ℝ, StrictMono L ∧ StrictMono w ∧
      (∀ i, 0 < w i ∧ w i < 1 ∧ L i*w i = h i) ∧
      ∀ y ∈ Y, IntervalRoom V L y := by
  have hsub : ({h} : Set (Fin m → ℝ)) ×ˢ Y ⊆ {p | IntervalRoom V p.1 p.2} := by
    rintro ⟨L,y⟩ ⟨hL,hy⟩
    have he : L = h := hL
    subst L
    exact hroom y hy
  obtain ⟨U,W,hU,_,hhU,hYW,hUW⟩ :=
    generalized_tube_lemma isCompact_singleton hY (intervalRoom_open V hV) hsub
  let d (i : Fin m) : ℝ := (m:ℝ)-(i:ℕ)
  have hd (i : Fin m) : 0 < d i := by
    dsimp [d]
    exact sub_pos.mpr (by exact_mod_cast i.isLt)
  let w (t : ℝ) (i : Fin m) := 1-t*d i
  let L (t : ℝ) (i : Fin m) := h i/w t i
  have hwc (i : Fin m) : Continuous (fun t => w t i) := by dsimp [w]; fun_prop
  have hLc : ContinuousAt L 0 := by
    apply continuousAt_pi.mpr
    intro i
    exact continuousAt_const.div (hwc i).continuousAt (by simp [w])
  have hL0 : L 0 = h := by ext i; simp [L,w]
  have heU : ∀ᶠ t in 𝓝 (0:ℝ), L t ∈ U := by
    apply hLc.tendsto.eventually
    rw [hL0]
    exact hU.mem_nhds (hhU rfl)
  have hemono : ∀ᶠ t in 𝓝 (0:ℝ), StrictMono (L t) := by
    apply hLc.tendsto.eventually
    rw [hL0]
    exact strictMono_open.mem_nhds hh
  have hepos : ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, 0 < w t i := by
    rw [eventually_all]
    intro i
    exact (hwc i).continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds (by simp [w]))
  obtain ⟨t,ht,htpos⟩ := (((heU.and (hemono.and hepos)).filter_mono
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).and self_mem_nhdsWithin).exists
  refine ⟨L t,w t,ht.2.1,?_,?_,?_⟩
  · intro i j hij
    have hij' : (i:ℝ) < (j:ℝ) := by exact_mod_cast hij
    dsimp [w,d]
    nlinarith only [mul_pos htpos (sub_pos.mpr hij')]
  · intro i
    refine ⟨ht.2.2 i,?_,?_⟩
    · dsimp [w]
      linarith only [mul_pos htpos (hd i)]
    · exact div_mul_cancel₀ _ (ht.2.2 i).ne'
  · intro y hy
    exact hUW (show (L t,y) ∈ U ×ˢ W from ⟨ht.1,hYW hy⟩)

theorem clampUnit_eq {h : ℝ} (hh : h ∈ Icc (0:ℝ) 1) : clampUnit h = h := by
  simp [clampUnit,min_eq_right hh.2,max_eq_right hh.1]

theorem unitRearrange_attained (F : C(P × ℝ,ℝ)) (y : P) {h : ℝ}
    (hh : h ∈ Icc (0:ℝ) 1) :
    ∃ a : ℝ, 0 ≤ a ∧ a+h ≤ 1 ∧ unitRearrange F (y,h) = max (F (y,a)) (F (y,a+h)) := by
  obtain ⟨t,ht⟩ := minimum_attained ((unitIntervalValue F).curry (y,h))
  refine ⟨t.val*(1-h),mul_nonneg t.property.1 (sub_nonneg.mpr hh.2),?_,?_⟩
  · nlinarith only [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hh.2)]
  · change minimum ((unitIntervalValue F).curry (y,h)) = _
    rw [←ht]
    simp [unitIntervalValue,clampUnit_eq hh]

theorem unitRearrange_le_candidate (F : C(P × ℝ,ℝ)) (y : P) {h a : ℝ}
    (hh : h ∈ Icc (0:ℝ) 1) (ha : 0 ≤ a) (hah : a+h ≤ 1) :
    unitRearrange F (y,h) ≤ max (F (y,a)) (F (y,a+h)) := by
  obtain ⟨t,ht⟩ := exists_unitInterval_mul (sub_nonneg.mpr hh.2) ha (by linarith)
  calc
    _ ≤ (unitIntervalValue F).curry (y,h) t := minimum_le _ t
    _ = _ := by simp [unitIntervalValue,clampUnit_eq hh,ht]

theorem unitRearrange_one (F : C(P × ℝ,ℝ)) (y : P) :
    unitRearrange F (y,1) = max (F (y,0)) (F (y,1)) := by
  obtain ⟨a,ha,hah,he⟩ := unitRearrange_attained F y (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  have ha0 : a = 0 := by linarith
  simpa [ha0] using he

theorem unitRearrange_mono (F : C(P × ℝ,ℝ)) (y : P)
    (hconv : ConvexOn ℝ (Icc 0 1) (fun v => F (y,v))) :
    MonotoneOn (fun h => unitRearrange F (y,h)) (Icc 0 1) := by
  intro h hh H hH hle
  obtain ⟨a,ha,haH,he⟩ := unitRearrange_attained F y hH
  have hah : a+h ≤ 1 := by linarith
  apply (unitRearrange_le_candidate F y hh ha hah).trans
  change max (F (y,a)) (F (y,a+h)) ≤ unitRearrange F (y,H)
  rw [he]
  apply max_le
  · exact le_max_left _ _
  · exact hconv.le_max_of_mem_Icc ⟨ha,by linarith [hH.1]⟩
      ⟨by linarith [hH.1],haH⟩ ⟨by linarith [hh.1],by linarith⟩

theorem unitSublevel_open (F : C(P × ℝ,ℝ)) (h ε : ℝ) :
    IsOpen {p : P × ℝ | p.2 ∈ unitSublevel F h ε p.1} :=
  (isOpen_Ioo.preimage continuous_snd).inter
    (isOpen_lt F.continuous (((unitRearrange F).continuous.comp
      (continuous_fst.prodMk continuous_const)).add continuous_const))

theorem unitSublevel_room (F : C(P × ℝ,ℝ)) (y : P) {h ε : ℝ}
    (hh : 0 ≤ h) (hh1 : h < 1) (he : 0 < ε) :
    ∃ u v : ℝ, u ∈ unitSublevel F h ε y ∧ v ∈ unitSublevel F h ε y ∧ h < v-u := by
  obtain ⟨a,ha,hah,hg⟩ := unitRearrange_attained F y ⟨hh,hh1.le⟩
  obtain ⟨u,v,hu,hv,huv,hfu,hfv⟩ := exists_longer_strict_interval
    (F.continuous.comp (continuous_const.prodMk continuous_id)) ha hah hh hh1
    (show F (y,a) < unitRearrange F (y,h)+ε by rw [hg]; linarith only [le_max_left (F (y,a)) (F (y,a+h)),he])
    (show F (y,a+h) < unitRearrange F (y,h)+ε by rw [hg]; linarith only [le_max_right (F (y,a)) (F (y,a+h)),he])
  exact ⟨u,v,⟨⟨hu,by linarith⟩,hfu⟩,⟨⟨by linarith,hv⟩,hfv⟩,huv⟩

theorem unitSublevel_convex (F : C(P × ℝ,ℝ)) (y : P)
    (hconv : ConvexOn ℝ (Icc 0 1) (fun v => F (y,v))) (h ε : ℝ) :
    Convex ℝ (unitSublevel F h ε y) := by
  have he : unitSublevel F h ε y = Ioo 0 1 ∩
      {v ∈ Icc 0 1 | F (y,v) < unitRearrange F (y,h)+ε} := by
    ext v
    exact ⟨fun hv => ⟨hv.1,⟨hv.1.1.le,hv.1.2.le⟩,hv.2⟩,
      fun hv => ⟨hv.1,hv.2.2⟩⟩
  rw [he]
  exact (convex_Ioo (𝕜 := ℝ) 0 1).inter (hconv.convex_lt _)

theorem unitSublevel_mono (F : C(P × ℝ,ℝ)) (y : P)
    (hconv : ConvexOn ℝ (Icc 0 1) (fun v => F (y,v))) (ε : ℝ) :
    MonotoneOn (fun h => unitSublevel F h ε y) (Icc 0 1) := by
  intro h hh H hH hle v hv
  refine ⟨hv.1,?_⟩
  have hg := unitRearrange_mono F y hconv hh hH hle
  change unitRearrange F (y,h) ≤ unitRearrange F (y,H) at hg
  linarith only [hv.2,hg]

end

theorem intervalMinimum_attained (f : C(ℝ,ℝ)) {L h : ℝ} (hh : h ∈ Icc 0 L) :
    ∃ a : ℝ, 0 ≤ a ∧ a+h ≤ L ∧ intervalMinimum f L h = max (f a) (f (a+h)) := by
  obtain ⟨t,ht⟩ := minimum_attained (fixedIntervalValue f L h)
  refine ⟨t.val*(L-h),mul_nonneg t.property.1 (sub_nonneg.mpr hh.2),?_,ht.symm⟩
  nlinarith only [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hh.2)]

theorem intervalMinimum_le_candidate (f : C(ℝ,ℝ)) {L h a : ℝ}
    (hh : h ∈ Icc 0 L) (ha : 0 ≤ a) (hah : a+h ≤ L) :
    intervalMinimum f L h ≤ max (f a) (f (a+h)) := by
  obtain ⟨t,ht⟩ := exists_unitInterval_mul (sub_nonneg.mpr hh.2) ha (by linarith)
  simpa only [intervalMinimum,fixedIntervalValue,ContinuousMap.coe_mk,ht] using minimum_le (fixedIntervalValue f L h) t

theorem intervalMinimum_shortening (f : C(ℝ,ℝ)) {L l h ε : ℝ}
    (_hl : 0 ≤ l) (hlL : l ≤ L) (hh : h ∈ Icc 0 l)
    (hm : ∀ s ∈ Icc (0:ℝ) L, ∀ t ∈ Icc (0:ℝ) L,
      |s-t| ≤ L-l → f s ≤ f t+ε) :
    intervalMinimum f l h ≤ intervalMinimum f L h+ε := by
  obtain ⟨a,ha,hah,he⟩ := intervalMinimum_attained f ⟨hh.1,hh.2.trans hlL⟩
  let b := min a (l-h)
  have hb : 0 ≤ b := le_min ha (sub_nonneg.mpr hh.2)
  have hbh : b+h ≤ l := by dsimp [b] <;> linarith [min_le_right a (l-h)]
  have hba : b ≤ a := min_le_left _ _
  have hab : a-b ≤ L-l := by
    dsimp [b]
    rcases le_total a (l-h) with hx | hx
    · rw [min_eq_left hx]; linarith
    · rw [min_eq_right hx]; linarith
  have h1 := hm b ⟨hb,by linarith [hh.1]⟩ a ⟨ha,by linarith [hh.1]⟩
    (by rw [abs_of_nonpos (sub_nonpos.mpr hba)]; linarith)
  have h2 := hm (b+h) ⟨by linarith [hh.1],hbh.trans hlL⟩ (a+h) ⟨by linarith [hh.1],hah⟩
    (by rw [abs_of_nonpos (by linarith)]; linarith)
  apply (intervalMinimum_le_candidate f hh hb hbh).trans
  rw [he]
  exact max_le ((h1.trans (add_le_add (le_max_left _ _) le_rfl)))
    (h2.trans (add_le_add (le_max_right _ _) le_rfl))

theorem intervalMinimum_outer_strip (f : C(ℝ,ℝ)) {L l h ε : ℝ}
    (hh : h ∈ Icc 0 L) (hlh : l ≤ h)
    (hm : ∀ s ∈ Icc (0:ℝ) L, ∀ t ∈ Icc (0:ℝ) L,
      |s-t| ≤ L-l → f s ≤ f t+ε) :
    f h ≤ intervalMinimum f L h+ε := by
  obtain ⟨a,ha,hah,he⟩ := intervalMinimum_attained f hh
  have h1 := hm h hh (a+h) ⟨by linarith [hh.1],hah⟩
    (by rw [abs_of_nonpos (by linarith)]; linarith)
  rw [he]
  exact h1.trans (add_le_add (le_max_right _ _) le_rfl)

theorem intervalMinimum_small (f : C(ℝ,ℝ)) {L h s ε : ℝ}
    (hh : h ∈ Icc 0 L) (hs : s ∈ Icc 0 L)
    (hm : ∀ u ∈ Icc (0:ℝ) L, ∀ v ∈ Icc (0:ℝ) L, f u ≤ f v+ε) :
    f s ≤ intervalMinimum f L h+ε := by
  obtain ⟨a,ha,hah,he⟩ := intervalMinimum_attained f hh
  rw [he]
  exact (hm s hs a ⟨ha,by linarith [hh.1]⟩).trans
    (add_le_add (le_max_left _ _) le_rfl)

variable {P : Type*} [TopologicalSpace P]

theorem unitRearrange_scaled (F : C(P × ℝ,ℝ)) (l : C(P,ℝ)) (y : P)
    (hl : 0 < l y) {h : ℝ} (hh : h ∈ Icc 0 (l y)) :
    unitRearrange (scaledUnitFamily F l) (y,h/l y) = intervalMinimum (fiberFunction F y) (l y) h := by
  have hq : h/l y ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg hh.1 hl.le,(div_le_one hl).mpr hh.2⟩
  change minimum ((unitIntervalValue (scaledUnitFamily F l)).curry (y,h/l y)) =
    minimum (fixedIntervalValue (fiberFunction F y) (l y) h)
  apply congrArg minimum
  apply ContinuousMap.ext
  intro t
  simp only [unitIntervalValue,ContinuousMap.coe_mk,ContinuousMap.curry_apply,
    clampUnit_eq hq,scaledUnitFamily,ContinuousMap.comp_apply,fiberFunction,fixedIntervalValue]
  congr 2 <;> field_simp

end PackingSufficiencySupport.Comparison
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_CartesianMomentSlices
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory
open Comparison
section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_smooth_nested_intervals_of_room {m : ℕ} {Y : Set P} (hY : IsClosed Y)
    (L : Fin m → ℝ) (hL : StrictMono L) (hpos : ∀ i, 0 < L i)
    (V : P → Fin m → Set ℝ)
    (hopen : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i})
    (hconv : ∀ y ∈ Y, ∀ i, Convex ℝ (V y i))
    (hnest : ∀ y ∈ Y, Monotone (V y)) (hsub : ∀ y i, V y i ⊆ Ioo 0 1)
    (hroom : ∀ y ∈ Y, IntervalRoom V L y) :
    ∃ c : P → Fin m → ℝ, ContDiff ℝ ∞ c ∧
      ∀ y ∈ Y, (∀ i, Icc (c y i) (c y i+L i) ⊆ V y i) ∧ StrictNestedStarts L (c y) := by
  apply exists_smooth_nested_intervals hY L hL V
    (fun i t => (hopen i).preimage (continuous_id.prodMk continuous_const)) hconv _ hpos
  intro y hy
  have hlo (i : Fin m) : BddBelow (V y i) := ⟨0,fun x hx => (hsub y i hx).1.le⟩
  have hhi (i : Fin m) : BddAbove (V y i) := ⟨1,fun x hx => (hsub y i hx).2.le⟩
  have hne (i : Fin m) : (V y i).Nonempty := by
    obtain ⟨a,_,ha,_,_⟩ := hroom y hy i
    exact ⟨a,ha⟩
  refine ⟨fun i => sInf (V y i),fun i => sSup (V y i),?_,?_,?_,?_⟩
  · intro i j hij
    exact csInf_le_csInf (hlo j) (hne i) (hnest y hy hij)
  · intro i j hij
    exact csSup_le_csSup (hhi j) (hne i) (hnest y hy hij)
  · intro i
    obtain ⟨a,b,ha,hb,hab⟩ := hroom y hy i
    exact hab.trans_le (sub_le_sub (le_csSup (hhi i) hb) (csInf_le (hlo i) ha))
  · intro i
    exact ((hconv y hy i).isConnected (hne i)).Ioo_csInf_csSup_subset (hlo i) (hhi i)

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_unit_grid {Y : Set P} (hY : IsCompact Y) (hcY : Convex ℝ Y)
    (y₀ : P) (hy₀ : y₀ ∈ Y) (F : C(P × ℝ,ℝ))
    (hconv : ∀ y ∈ Y, ConvexOn ℝ (Icc 0 1) (fun v => F (y,v)))
    {m : ℕ} (h : Fin m → ℝ) (hh : StrictMono h)
    (hpos : ∀ i, 0 < h i) (hbound : ∀ i, h i < 1) {ε : ℝ} (he : 0 < ε) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1), ∀ i y, y ∈ Y →
      ∀ x ∈ closedRoundDisk (areaRadius (h i)),
        F (y,radialArea (Ψ.isotopy.map y 1 x)) < unitRearrange F (y,h i)+ε := by
  let V (y : P) (i : Fin m) := unitSublevel F (h i) ε y
  have hopen : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i} :=
    fun i => unitSublevel_open F (h i) ε
  have hsub (y : P) (i : Fin m) : V y i ⊆ Ioo 0 1 := fun _ hv => hv.1
  have hvconv (y : P) (hy : y ∈ Y) (i : Fin m) : Convex ℝ (V y i) :=
    unitSublevel_convex F y (hconv y hy) (h i) ε
  have hnest (y : P) (hy : y ∈ Y) : Monotone (V y) := by
    intro i j hij
    exact unitSublevel_mono F y (hconv y hy) ε ⟨(hpos i).le,(hbound i).le⟩
      ⟨(hpos j).le,(hbound j).le⟩ (hh.monotone hij)
  have hroom (y : P) (_ : y ∈ Y) : IntervalRoom V h y :=
    fun i => unitSublevel_room F y (hpos i).le (hbound i) he
  obtain ⟨L,w,hLmono,hwmono,hw,hrooms⟩ := exists_uniform_interval_widths hY h hh V hopen hroom
  have hLpos (i : Fin m) : 0 < L i :=
    (mul_pos_iff_of_pos_right (hw i).1).mp ((hw i).2.2 ▸ hpos i)
  obtain ⟨c,hc,hplace⟩ := exists_smooth_nested_intervals_of_room hY.isClosed
    L hLmono hLpos V hopen hvconv hnest hsub hrooms
  have hp (y : P) (hy : y ∈ Y) :
      (∀ i, c y i ∈ V y i ∧ c y i+L i ∈ V y i) ∧ StrictNestedStarts L (c y) := by
    refine ⟨fun i => ?_,(hplace y hy).2⟩
    have hle : c y i ≤ c y i+L i := le_add_of_nonneg_right (hLpos i).le
    exact ⟨(hplace y hy).1 i ⟨le_rfl,hle⟩,(hplace y hy).1 i ⟨hle,le_rfl⟩⟩
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_rounded_intervals_bp240 hY hcY y₀ hy₀ h L w
    hpos hbound hh (fun i => (hw i).1) (fun i => (hw i).2.1) hwmono
    (fun i => (hw i).2.2) c hc V hopen hvconv hsub hp
  exact ⟨Ψ,fun i y hy x hx => (hΨ i y hy x hx).2⟩

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Comparison
open Set

theorem exists_fine_unit_grid {δ : ℝ} (hδ : 0 < δ) :
    ∃ (m : ℕ) (h : Fin m → ℝ), StrictMono h ∧ (∀ i, 0 < h i ∧ h i < 1) ∧
      ∀ v ∈ Icc (0:ℝ) 1, (∃ i, v ≤ h i ∧ h i-v < δ) ∨ 1-v < δ := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/δ)
  have hd : 0 < (N:ℝ)+1 := by positivity
  have hstep : 1/((N:ℝ)+1) < δ := (one_div_lt hd hδ).2 (by linarith)
  let h (i : Fin N) : ℝ := ((i:ℕ)+1 : ℝ)/((N:ℝ)+1)
  refine ⟨N,h,?_,?_,?_⟩
  · intro i j hij
    apply (div_lt_div_iff_of_pos_right hd).2
    have hij' : (i:ℝ) < (j:ℝ) := by exact_mod_cast hij
    change (i:ℝ)+1 < (j:ℝ)+1
    linarith
  · intro i
    constructor
    · exact div_pos (by positivity) hd
    · apply (div_lt_one hd).2
      have hi : (i:ℝ) < (N:ℝ) := by exact_mod_cast i.isLt
      change (i:ℝ)+1 < (N:ℝ)+1
      linarith
  · intro v hv
    let k := ⌊v*((N:ℝ)+1)⌋₊
    have hk : (k:ℝ) ≤ v*((N:ℝ)+1) := Nat.floor_le (mul_nonneg hv.1 hd.le)
    have hk' : v*((N:ℝ)+1) < (k:ℝ)+1 := Nat.lt_floor_add_one _
    by_cases hsmall : k < N
    · left
      refine ⟨⟨k,hsmall⟩,?_,?_⟩
      · exact ((le_div_iff₀ hd).2 hk'.le)
      · apply lt_of_le_of_lt _ hstep
        apply (le_div_iff₀ hd).2
        change (((k:ℝ)+1)/((N:ℝ)+1)-v)*((N:ℝ)+1) ≤ 1
        rw [sub_mul,div_mul_cancel₀ _ hd.ne']
        linarith
    · right
      have hNk : (N:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.le_of_not_gt hsmall
      apply lt_of_le_of_lt _ hstep
      apply (le_div_iff₀ hd).2
      nlinarith only [hk,hNk]

variable {P : Type*} [PseudoMetricSpace P]

theorem exists_uniform_unit_modulus {Y : Set P} (hY : IsCompact Y)
    (G : C(P × ℝ,ℝ)) {ε : ℝ} (he : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Y, ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1,
      |u-v| < δ → G (y,u) < G (y,v)+ε := by
  have hc := (hY.prod (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))).uniformContinuousOn_of_continuous
    G.continuous.continuousOn
  obtain ⟨δ,hδ,hG⟩ := Metric.uniformContinuousOn_iff.mp hc ε he
  refine ⟨δ,hδ,?_⟩
  intro y hy u hu v hv hd
  have hdist : dist (y,u) (y,v) < δ := by
    simpa only [Prod.dist_eq,dist_self,Real.dist_eq,max_eq_right (abs_nonneg (u-v))] using hd
  have hh := hG (y,u) ⟨hy,hu⟩ (y,v) ⟨hy,hv⟩ hdist
  rw [Real.dist_eq] at hh
  linarith only [(le_abs_self (G (y,u)-G (y,v))).trans_lt hh]

end PackingSufficiencySupport.Comparison

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open Comparison
open scoped BigOperators
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_unit_rearrangement {Y : Set P}
    (hY : IsCompact Y) (hcY : Convex ℝ Y) (F : C(P × ℝ,ℝ))
    (hconv : ∀ y ∈ Y, ConvexOn ℝ (Icc 0 1) (fun v => F (y,v)))
    {ε : ℝ} (he : 0 < ε) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1), ∀ y ∈ Y,
      ∀ x ∈ closedRoundDisk (areaRadius 1),
        F (y,radialArea (Ψ.isotopy.map y 1 x)) ≤ unitRearrange F (y,radialArea x)+ε := by
  rcases Y.eq_empty_or_nonempty with hzero | ⟨y₀,hy₀⟩
  · refine ⟨HamiltonianDiskIsotopyFamily.refl _,?_⟩
    simp [hzero]
  have he2 : 0 < ε/2 := half_pos he
  obtain ⟨δ,hδ,hmod⟩ := exists_uniform_unit_modulus hY (unitRearrange F) he2
  obtain ⟨m,h,hh,hhi,hcover⟩ := exists_fine_unit_grid hδ
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_unit_grid hY hcY y₀ hy₀ F hconv h hh
    (fun i => (hhi i).1) (fun i => (hhi i).2) he2
  refine ⟨Ψ,?_⟩
  intro y hy x hx
  have hx1 : radialArea x ∈ Icc (0:ℝ) 1 :=
    ⟨radialArea_nonneg x,(mem_closedRoundDisk_areaRadius (by norm_num) x).mp hx⟩
  rcases hcover (radialArea x) hx1 with ⟨i,hle,hd⟩ | hd
  · have hxmem : x ∈ closedRoundDisk (areaRadius (h i)) :=
      (mem_closedRoundDisk_areaRadius (hhi i).1.le x).mpr hle
    have hf := hΨ i y hy x hxmem
    have hg := hmod y hy (h i) ⟨(hhi i).1.le,(hhi i).2.le⟩ (radialArea x) hx1
      (by rwa [abs_of_nonneg (sub_nonneg.mpr hle)])
    linarith
  · have hxmap := Ψ.mapsTo_closed y 1 hx
    have hm : radialArea (Ψ.isotopy.map y 1 x) ∈ Icc (0:ℝ) 1 :=
      ⟨radialArea_nonneg _,(mem_closedRoundDisk_areaRadius (by norm_num) _).mp hxmap⟩
    have hf := (hconv y hy).le_max_of_mem_Icc (show (0:ℝ) ∈ Icc 0 1 by norm_num)
      (show (1:ℝ) ∈ Icc 0 1 by norm_num) hm
    rw [←unitRearrange_one F y] at hf
    have hg := hmod y hy 1 ⟨zero_le_one,le_rfl⟩ (radialArea x) hx1
      (by rwa [abs_of_nonneg (sub_nonneg.mpr hx1.2)])
    linarith

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_LiftedCompact
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Comparison
open Set

variable {P : Type*} [PseudoMetricSpace P]

theorem exists_uniform_variable_modulus {Y : Set P} (hY : IsCompact Y)
    {L : P → ℝ} (hL : ContinuousOn L Y) (G : C(P × ℝ,ℝ)) {ε : ℝ} (he : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Y, ∀ u ∈ Icc (0:ℝ) (L y), ∀ v ∈ Icc (0:ℝ) (L y),
      |u-v| < δ → G (y,u) < G (y,v)+ε := by
  obtain ⟨M,hM⟩ := (hY.image_of_continuousOn hL).bddAbove
  have hc := (hY.prod (isCompact_Icc : IsCompact (Icc (0:ℝ) M))).uniformContinuousOn_of_continuous
    G.continuous.continuousOn
  obtain ⟨δ,hδ,hG⟩ := Metric.uniformContinuousOn_iff.mp hc ε he
  refine ⟨δ,hδ,?_⟩
  intro y hy u hu v hv hd
  have hdist : dist (y,u) (y,v) < δ := by
    simpa only [Prod.dist_eq,dist_self,Real.dist_eq,max_eq_right (abs_nonneg (u-v))] using hd
  have hh := hG (y,u) ⟨hy,hu.1,hu.2.trans (hM ⟨y,hy,rfl⟩)⟩
    (y,v) ⟨hy,hv.1,hv.2.trans (hM ⟨y,hy,rfl⟩)⟩ hdist
  rw [Real.dist_eq] at hh
  linarith only [(le_abs_self (G (y,u)-G (y,v))).trans_lt hh]

end PackingSufficiencySupport.Comparison

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open Comparison
open scoped BigOperators
open MeasureTheory
section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_smooth_positive_shortening {Y : Set P} (hY : IsClosed Y)
    {L : P → ℝ} (hL : Continuous L) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hLY : ∀ y ∈ Y, η ≤ L y) :
    ∃ l : P → ℝ, ContDiff ℝ ∞ l ∧ (∀ y, 0 < l y) ∧
      ∀ y ∈ Y, η/2 < l y ∧ L y-δ < l y ∧ l y < L y := by
  let S : P → Set ℝ := fun y => {r | 0 < r ∧ (y ∈ Y → η/2 < r ∧ L y-δ < r ∧ r < L y)}
  have hs (r : ℝ) : IsOpen {y | r ∈ S y} := by
    by_cases hr : 0 < r
    · have he : {y | r ∈ S y} = Yᶜ ∪ {y | η/2 < r ∧ L y-δ < r ∧ r < L y} := by
        ext y; simp [S,hr,or_iff_not_imp_left]
      rw [he]
      exact hY.isOpen_compl.union ((isOpen_const).inter
        ((isOpen_lt (hL.sub continuous_const) continuous_const).inter
          (isOpen_lt continuous_const hL)))
    · simp [S,hr]
  have hc (y : P) (_ : y ∈ (univ : Set P)) : Convex ℝ (S y) := by
    by_cases hy : y ∈ Y
    · have he : S y = Ioi 0 ∩ (Ioi (η/2) ∩ (Ioi (L y-δ) ∩ Iio (L y))) := by
        ext r; simp [S,hy]
      rw [he]
      exact (convex_Ioi (0:ℝ)).inter ((convex_Ioi _).inter ((convex_Ioi _).inter (convex_Iio _)))
    · have he : S y = Ioi 0 := by ext r; simp [S,hy]
      rw [he]
      exact convex_Ioi (𝕜 := ℝ) (0:ℝ)
  have hn (y : P) (_ : y ∈ (univ : Set P)) : (S y).Nonempty := by
    by_cases hy : y ∈ Y
    · have hm : max (η/2) (L y-δ) < L y := max_lt (by linarith [hLY y hy]) (by linarith)
      obtain ⟨r,hr,hrL⟩ := exists_between hm
      exact ⟨r,by linarith [le_max_left (η/2) (L y-δ)],fun _ =>
        ⟨(le_max_left _ _).trans_lt hr,(le_max_right _ _).trans_lt hr,hrL⟩⟩
    · exact ⟨1,by norm_num,fun h => (hy h).elim⟩
  obtain ⟨l,hl,hlS⟩ := exists_smooth_convex_selection isClosed_univ S hs hc hn
  exact ⟨l,hl,fun y => (hlS y (mem_univ _)).1,fun y hy => (hlS y (mem_univ _)).2 hy⟩

theorem exists_shortening_cutoff {K : Set P} (hK : IsCompact K)
    {L l : P → ℝ} (hL : Continuous L) (hl : Continuous l) {η δ : ℝ}
    (hKbounds : ∀ y ∈ K, η < L y ∧ η/2 < l y ∧ L y-δ < l y ∧ l y < L y) :
    ∃ χ : P → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ y, χ y ∈ Icc 0 1) ∧ (∀ y ∈ K, χ y = 1) ∧
      ∀ y ∈ tsupport χ, η < L y ∧ η/2 < l y ∧ L y-δ < l y ∧ l y < L y := by
  let U := {y | η < L y ∧ η/2 < l y ∧ L y-δ < l y ∧ l y < L y}
  have hU : IsOpen U := (isOpen_lt continuous_const hL).inter
    ((isOpen_lt continuous_const hl).inter ((isOpen_lt (hL.sub continuous_const) hl).inter
      (isOpen_lt hl hL)))
  obtain ⟨χ,hχ,hχc,hχU,hχ1,hr⟩ := exists_smooth_cutoff hK hU hKbounds
  refine ⟨χ,hχ,hχc,hr,?_,hχU⟩
  intro y hy
  exact hχ1.self_of_nhdsSet y hy

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem scaledUnitFamily_convex (F : C(P × ℝ,ℝ)) (l : C(P,ℝ)) (y : P) {L : ℝ}
    (hl : 0 ≤ l y) (hlL : l y ≤ L)
    (hF : ConvexOn ℝ (Icc 0 L) (fun v => F (y,v))) :
    ConvexOn ℝ (Icc 0 1) (fun v => scaledUnitFamily F l (y,v)) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro u hu v hv a b ha hb hab
  have hmul (w : ℝ) (hw : w ∈ Icc (0:ℝ) 1) : l y*w ∈ Icc (0:ℝ) L :=
    ⟨mul_nonneg hl hw.1,(mul_le_of_le_one_right hl hw.2).trans hlL⟩
  have hh := hF.2 (hmul u hu) (hmul v hv) ha hb hab
  simp only [smul_eq_mul] at hh
  change F (y,l y*(a*u+b*v)) ≤ a*F (y,l y*u)+b*F (y,l y*v)
  have hlin : l y*(a*u+b*v) = a*(l y*u)+b*(l y*v) := by ring
  rw [hlin]
  exact hh

omit [FiniteDimensional ℝ P] in

theorem scaled_trace_inner_estimate (F : C(P × ℝ,ℝ)) (l : C(P,ℝ))
    (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1)) {a χ : P → ℝ}
    (y : P) (ha : 0 < a y) (hal : (a y)^2 = l y) (hχ : χ y = 1)
    {ε : ℝ}
    (hΨ : ∀ x ∈ closedRoundDisk (areaRadius 1),
      scaledUnitFamily F l (y,radialArea (Ψ.isotopy.map y 1 x)) ≤
        unitRearrange (scaledUnitFamily F l) (y,radialArea x)+ε)
    (x : Plane) (hx : radialArea x ≤ l y) :
    F (y,radialArea (scaledPlanarTrace Ψ.motion a χ y 1 x)) ≤
      intervalMinimum (fiberFunction F y) (l y) (radialArea x)+ε := by
  have hl : 0 < l y := hal ▸ sq_pos_of_pos ha
  have hs : radialArea ((a y)⁻¹ • x) = radialArea x/l y := by
    rw [radialArea_smul,←hal]
    field_simp
  have hm : (a y)⁻¹ • x ∈ closedRoundDisk (areaRadius 1) := by
    rw [mem_closedRoundDisk_areaRadius (by norm_num),hs]
    exact (div_le_one hl).mpr hx
  have hh := hΨ _ hm
  rw [hs,unitRearrange_scaled F l y hl ⟨radialArea_nonneg x,hx⟩] at hh
  rw [scaledPlanarTrace_time_one Ψ.motion y hχ,radialArea_smul,hal]
  exact hh

theorem exists_scaled_slice_rearrangement_bp240_oai {Y : Set P} (hY : IsCompact Y)
    {L : P → ℝ} (hL : Continuous L) (hcL : ConcaveOn ℝ Y L)
    (F : C(P × ℝ,ℝ))
    (hconv : ∀ y ∈ Y, ConvexOn ℝ (Icc 0 (L y)) (fun v => F (y,v)))
    {ε : ℝ} (he : 0 < ε) :
    ∃ (a χ : P → ℝ) (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1)),
      ContDiff ℝ ∞ a ∧ (∀ y, 0 < a y) ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ y, χ y ∈ Icc 0 1) ∧
      (∀ y ∈ tsupport χ, (a y)^2 < L y) ∧
      (∀ y ∈ Y, ∀ t x, radialArea x ≤ L y →
        radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ L y) ∧
      (∀ y ∈ Y, ∀ x, radialArea x ≤ L y →
        F (y,radialArea (scaledPlanarTrace Ψ.motion a χ y 1 x)) ≤
          intervalMinimum (fiberFunction F y) (L y) (radialArea x)+ε) := by
  obtain ⟨δ,hδ,hm⟩ := exists_uniform_variable_modulus hY hL.continuousOn F (half_pos he)
  let η := δ/4
  have hη : 0 < η := div_pos hδ (by norm_num)
  let A := {y ∈ Y | η ≤ L y}
  have hA : IsCompact A := hY.inter_right (isClosed_le continuous_const hL)
  have hcA : Convex ℝ A := hcL.convex_ge η
  obtain ⟨l,hl,hlpos,hlA⟩ := exists_smooth_positive_shortening hA.isClosed hL hη
    (half_pos hδ) (fun y (hy : y ∈ A) => hy.2)
  let K := {y ∈ Y | 2*η ≤ L y}
  have hK : IsCompact K := hY.inter_right (isClosed_le continuous_const hL)
  have hKA : K ⊆ A := fun y hy => ⟨hy.1,by linarith [hy.2]⟩
  obtain ⟨χ,hχ,hχc,hχrange,hχone,hχfit⟩ := exists_shortening_cutoff hK hL hl.continuous
    (η := η) (δ := δ/2) (by
      intro y hy
      exact ⟨by linarith [hy.2],hlA y (hKA hy)⟩)
  let a := fun y => Real.sqrt (l y)
  have ha : ContDiff ℝ ∞ a := hl.sqrt (fun y => (hlpos y).ne')
  have hapos (y : P) : 0 < a y := Real.sqrt_pos.mpr (hlpos y)
  have hal (y : P) : (a y)^2 = l y := Real.sq_sqrt (hlpos y).le
  let lc : C(P,ℝ) := ⟨l,hl.continuous⟩
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_unit_rearrangement hA hcA (scaledUnitFamily F lc)
    (fun y hy => scaledUnitFamily_convex F lc y (hlpos y).le (hlA y hy).2.2.le
      (hconv y hy.1)) (half_pos he)
  have hfit (y : P) (hy : y ∈ tsupport χ) : (a y)^2 < L y := by
    rw [hal]; exact (hχfit y hy).2.2.2
  have hpres (y : P) (t : ℝ) (x : Plane) (hx : radialArea x ≤ L y) :
      radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ L y :=
    scaled_disk_preserves_slice Ψ y (hapos y).ne' t x hx
      (fun h => (hfit y (subset_tsupport χ h)).le)
  refine ⟨a,χ,Ψ,ha,hapos,hχ,hχc,hχrange,hfit,fun y _ => hpres y,?_⟩
  intro y hy x hx
  have hxI : radialArea x ∈ Icc (0:ℝ) (L y) := ⟨radialArea_nonneg x,hx⟩
  by_cases hlarge : 2*η ≤ L y
  · have hyK : y ∈ K := ⟨hy,hlarge⟩
    have hyA : y ∈ A := hKA hyK
    have hm' (s : ℝ) (hs : s ∈ Icc (0:ℝ) (L y)) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (L y))
        (hd : |s-t| ≤ L y-l y) : fiberFunction F y s ≤ fiberFunction F y t+ε/2 :=
      (hm y hy s hs t ht (by linarith [(hlA y hyA).2.1])).le
    rcases le_total (radialArea x) (l y) with hinner | houter
    · have hj := scaled_trace_inner_estimate F lc Ψ y (hapos y) (hal y) (hχone y hyK)
        (hΨ y hyA) x hinner
      dsimp only [lc,ContinuousMap.coe_mk] at hj
      have hs := intervalMinimum_shortening (fiberFunction F y) (hlpos y).le
        (hlA y hyA).2.2.le ⟨radialArea_nonneg x,hinner⟩ hm'
      linarith
    · rw [scaled_disk_fixed Ψ y (hapos y).ne' 1 x (by rw [hal]; exact houter)]
      have hs := intervalMinimum_outer_strip (fiberFunction F y) hxI houter hm'
      change F (y,radialArea x) ≤ _ at hs
      linarith
  · have hsmall : L y < 2*η := lt_of_not_ge hlarge
    have hm' (u : ℝ) (hu : u ∈ Icc (0:ℝ) (L y)) (v : ℝ) (hv : v ∈ Icc (0:ℝ) (L y)) :
        fiberFunction F y u ≤ fiberFunction F y v+ε/2 := by
      apply (hm y hy u hu v hv ?_).le
      rw [abs_lt]
      dsimp [η] at hsmall
      constructor <;> linarith [hu.1,hu.2,hv.1,hv.2]
    have hs := intervalMinimum_small (fiberFunction F y) hxI
      ⟨radialArea_nonneg _,hpres y 1 x hx⟩ hm'
    change F (y,radialArea (scaledPlanarTrace Ψ.motion a χ y 1 x)) ≤ _ at hs
    linarith

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.exists_scaled_slice_rearrangement_bp240_oai := @OAI.PackingSufficiencySupport.Hamiltonian.exists_scaled_slice_rearrangement_bp240_oai
