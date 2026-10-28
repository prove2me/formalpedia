-- Prove2me | solution 1 for OAI.ScalarConductivity.PhysicalFiniteEndingData.endRepresentative_regular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:07:11.921706+00:00
-- url     : https://prove2.me/submissions/195d707e-862a-4ab4-9552-4cab3da28a7b

import Mathlib
import Definitions.Def_OAIQ059C008

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_LocalSmoothSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

lemma local_iteratedFDeriv_tsum {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ι → E → F} {s : Set E} (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ i, ContDiff ℝ (↑(⊤:ℕ∞)) (f i))
    (v : ℕ → ι → ℝ) (hv : ∀ n, Summable (v n))
    (hbound : ∀ n i x, x∈s → ‖iteratedFDeriv ℝ n (f i) x‖≤v n i)
    (n : ℕ) {x : E} (hx : x∈s) :
    iteratedFDeriv ℝ n (fun x => ∑' i, f i x) x = ∑' i, iteratedFDeriv ℝ n (f i) x := by
  have ht := (local_smooth_taylor hs hsc hf v hv hbound).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)) (hs.uniqueDiffOn) hx
  rw [iteratedFDerivWithin_of_isOpen n hs hx] at ht
  exact ht.symm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFourierSmooth
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma flatFourier_iterated {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h, |a h|≤B)
    (n : ℕ) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    iteratedFDeriv ℝ n (flatFourier s a phase) x =
      ∑' h, iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) x := by
  apply local_iteratedFDeriv_tsum (axial_halfspace_open (x 0/2)) (axial_halfspace_connected (x 0/2))
    (fun h => contDiff_const.mul (flatPhaseMode_smooth s h (phase h)))
    (fun n h => B*((torusRate s h+torusSize h)^n*exp (-(x 0/2)*torusRate s h)))
  · intro n
    exact (flatMode_derivative_summable hs n (by linarith)).mul_left B
  · intro n h y hy
    exact weighted_phase_halfspace_bound ha n h hy.le
  · change x 0/2<x 0
    linarith

lemma flatFourier_iterated_norm {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B δ : ℝ} (ha : ∀ h, |a h|≤B) (hδ : 0<δ)
    (n : ℕ) {x : Fin 3 → ℝ} (hx : δ≤x 0) :
    ‖iteratedFDeriv ℝ n (flatFourier s a phase) x‖≤
      ∑' h, B*((torusRate s h+torusSize h)^n*exp (-δ*torusRate s h)) := by
  rw [flatFourier_iterated hs ha n (hδ.trans_le hx)]
  have hb := (flatMode_derivative_summable hs n hδ).mul_left B
  have hn : Summable (fun h => ‖iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) x‖) := Summable.of_nonneg_of_le (fun h => norm_nonneg _)
    (fun h => weighted_phase_halfspace_bound ha n h hx) hb
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (fun h => weighted_phase_halfspace_bound ha n h hx) hb)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactDepthReductionTwo
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma TwoFieldRankRegular.mono {u : Coord3 → Fin 2 → ℝ} {O W : Set Coord3}
    (h : TwoFieldRankRegular u O) (hW : W ⊆ O) : TwoFieldRankRegular u W := by
  rcases h with h | h | ⟨κ, hκ⟩
  · exact Or.inl (fun x hx => h x (hW hx))
  · obtain ⟨v, l, κ, hv, hl, hd, he⟩ := h
    exact Or.inr (Or.inl ⟨v, l, κ, hv.mono hW, hl, fun x hx => hd x (hW hx),
      fun x hx => he x (hW hx)⟩)
  · exact Or.inr (Or.inr ⟨κ, fun x hx => hκ x (hW hx)⟩)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPatch
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma TwoFieldRankRegular.congr {u v : Coord3 → Fin 2 → ℝ} {O : Set Coord3}
    (hO : IsOpen O) (h : TwoFieldRankRegular u O) (he : EqOn v u O) :
    TwoFieldRankRegular v O := by
  rcases h with h | h | ⟨κ,hκ⟩
  · left
    intro x hx
    rw [fderiv_eq_of_eqOn_open hO he hx]
    exact h x hx
  · right; left
    obtain ⟨w,l,κ,hw,hl,hwd,hrel⟩ := h
    exact ⟨w,l,κ,hw,hl,hwd,fun x hx j => by rw [he hx]; exact hrel x hx j⟩
  · exact Or.inr (Or.inr ⟨κ,fun x hx => (he hx).trans (hκ x hx)⟩)

lemma RegularPatch.mono {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {O W : Set Coord3} (h : RegularPatch u A O) (hW : IsOpen W) (hWO : W ⊆ O) :
    RegularPatch u A W :=
  ⟨hW,h.2.1.mono hWO,h.2.2.1.mono hWO,h.2.2.2.mono hWO⟩

lemma RegularPatch.congr {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    {O : Set Coord3} (h : RegularPatch u A O) (hu : EqOn v u O) (hA : EqOn B A O) :
    RegularPatch v B O := by
  exact ⟨h.1,h.2.1.congr hu,h.2.2.1.congr (fun x hx => congrArg Subtype.val (hA hx)),
    h.2.2.2.congr h.1 hu⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_CascadeConstitution
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma ae_coord3_ne (i : Fin 3) (r : ℝ) : ∀ᵐ x : Coord3, x i≠r := by
  exact MeasureTheory.Measure.ae_eval_ne (fun _ : Fin 3 => (volume : Measure ℝ)) i r

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPatchTranslation
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma mem_regularRegion_congr_nhds {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    {V U : Set Coord3} {x : Coord3} (h : x∈regularRegion u A V)
    (hu : v =ᶠ[𝓝 x] u) (hA : B =ᶠ[𝓝 x] A) (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion v B U := by
  obtain ⟨O,hOV,hO,hxO⟩ := mem_regularRegion_iff.mp h
  have hh : {y | y∈O ∧ y∈U ∧ v y=u y ∧ B y=A y}∈𝓝 x := by
    filter_upwards [hO.1.mem_nhds hxO,hU.mem_nhds hx,hu,hA] with y hy0 hyU hyu hyA
    exact ⟨hy0,hyU,hyu,hyA⟩
  obtain ⟨W,hWsub,hW,hxW⟩ := mem_nhds_iff.mp hh
  refine mem_regularRegion_iff.mpr ⟨W,fun y hy => (hWsub hy).2.1,?_,hxW⟩
  exact (hO.mono hW (fun y hy => (hWsub hy).1)).congr
    (fun y hy => (hWsub hy).2.2.1) (fun y hy => (hWsub hy).2.2.2)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFaceUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma squareFace_interior_unique (i k : Fin 4) {a b : ℝ} (ha : |a|<1)
    (he : squareFace i a=squareFace k b) : i=k := by
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have ha₁ := (abs_lt.mp ha).1
  have ha₂ := (abs_lt.mp ha).2
  fin_cases i <;> fin_cases k <;>
    simp [squareFace,squareFaceBase,squareFaceDirection] at h0 h1 ⊢ <;> linarith

lemma sourceCollarPiece_open_unique (i j k l : Fin 4) {x z : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox)
    (hz : z∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (he : sourceCollarPiece i j x=sourceCollarPiece k l z) : i=k ∧ j=l := by
  obtain ⟨hzt,hza,hzb⟩ := mem_sourceExtendedBox.mp hz
  have hx' := sourceCollarOpenBox_subset hx
  obtain ⟨hxt,hxa,hxb⟩ := mem_sourceExtendedBox.mp hx'
  have hxR : 0 < sourceCollarRadius j (x 0) (x 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended j hxt hxb).1
  have hzR : 0 < sourceCollarRadius l (z 0) (z 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended l hzt hzb).1
  have hR : sourceCollarRadius j (x 0) (x 2)=sourceCollarRadius l (z 0) (z 2) := by
    have hh := congrArg sourceRadial he
    rwa [sourceCollarPiece_radial_pos i j hxR.le hxa,
      sourceCollarPiece_radial_pos k l hzR.le hza] at hh
  have ht : x 0=z 0 := by
    have hh := congrArg sourceCollarTime he
    rwa [sourceCollarPiece_time_pos i j hxR.le (by linarith [hxt.2]) hxa hxb,
      sourceCollarPiece_time_pos k l hzR.le (by linarith [hzt.2]) hza hzb] at hh
  constructor
  · apply squareFace_interior_unique i k hx.2.1
    have hh := congrArg (fun y : Fin 3 → ℝ => ![y 0/sourceLength,y 1]) he
    rw [sourceCollarPiece_angular,sourceCollarPiece_angular,←hR] at hh
    exact smul_right_injective (Fin 2 → ℝ) hxR.ne' hh
  · apply squareFace_interior_unique j l hx.2.2
    have hh := congrArg sourceCrossCoordinates he
    rw [sourceCollarPiece_cross_pos i j hxR.le hxa,
      sourceCollarPiece_cross_pos k l hzR.le hza,←ht] at hh
    exact smul_right_injective (Fin 2 → ℝ) (by linarith [hxt.2] : 1-x 0≠0) hh

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTestEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceExtendedBox_open_ae {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x∈sourceCollarOpenBox := by
  let B := sourceExtendedBox (-(1:ℝ)/100) (1/100)
  have hB : volume (frontier B)=0 := (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier B := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc),
    ae_restrict_of_ae hn] with x hx hn
  have hxB : x∈B := by
    obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp hx
    exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,hi,hj⟩
  rw [sourceCollarOpenBox_eq_interior]
  by_contra h
  exact hn ⟨subset_closure hxB,h⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullWeakEndEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceCollarClosedPiece_measurable (l r : ℝ) (i j : Fin 4) :
    MeasurableSet (sourceCollarPiece i j '' sourceExtendedBox l r) :=
  (isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous).measurableSet

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullEndClosedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceExtendedBox_interior_axial {l r : ℝ} {x : Fin 3 → ℝ}
    (hx : x∈interior (sourceExtendedBox l r)) : x 0∈Ioo l r := by
  have hbox : sourceExtendedBox l r=
      (univ : Set (Fin 3)).pi (fun k => Icc (![l,-1,-1] k) (![r,1,1] k)) := by
    ext x
    simp only [sourceExtendedBox,mem_Icc,Set.mem_pi,mem_univ,true_implies,Pi.le_def]
    simp only [forall_and]
  rw [hbox,interior_pi_set (finite_univ)] at hx
  have ht := hx 0 (mem_univ 0)
  simpa only [interior_Icc,Matrix.cons_val_zero] using ht

lemma sourceExtendedBox_axial_strict_ae (l r : ℝ) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x 0∈Ioo l r := by
  have hB : volume (frontier (sourceExtendedBox l r))=0 :=
    (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier (sourceExtendedBox l r) := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_of_ae hn,
    ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc)] with x hx hm
  apply sourceExtendedBox_interior_axial
  by_contra hi
  exact hx ⟨subset_closure hm,hi⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AnalyticDerivativeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology
open scoped NNReal ENNReal

theorem analyticAt_of_factorial_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {a : E} {R M C : ℝ} (hR : 0<R) (hM : 0≤M) (hC : 0<C)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞)) f (Metric.ball a R))
    (hb : ∀ n : ℕ, ∀ x∈Metric.ball a R,
      ‖iteratedFDeriv ℝ n f x‖≤M*C^n*(n.factorial : ℝ)) : AnalyticAt ℝ f a := by
  let p : FormalMultilinearSeries ℝ E F := fun n => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n f a
  let r : ℝ≥0 := ⟨min R (1/C)/2,by positivity⟩
  have hr : 0<(r : ℝ) := by change 0 < min R (1/C)/2; positivity
  have hrR : (r : ℝ)<R := by
    change min R (1/C)/2<R
    have := min_le_left R (1/C)
    linarith
  have hrC : (r : ℝ)<1/C := by
    change min R (1/C)/2<1/C
    have := min_le_right R (1/C)
    have : 0<1/C := by positivity
    linarith
  have hp (n : ℕ) : ‖p n‖≤M*C^n := by
    dsimp [p]
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (n.factorial : ℝ)⁻¹*(M*C^n*(n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hb n a (by simpa using hR)) (by positivity)
      _ = M*C^n := by
        have hn : (n.factorial : ℝ)≠0 := by positivity
        field_simp
  have hrad : (r : ℝ≥0∞)≤p.radius := by
    apply p.le_radius_of_bound M
    intro n
    calc
      ‖p n‖*(r : ℝ)^n ≤ M*C^n*(r : ℝ)^n := mul_le_mul_of_nonneg_right (hp n) (by positivity)
      _ = M*(C*(r : ℝ))^n := by rw [mul_pow]; ring
      _ ≤ M*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity)
        (by nlinarith [(lt_div_iff₀ hC).mp hrC])) hM
      _ = M := mul_one _
  refine ⟨p,⟨r,⟨hrad,by exact_mod_cast hr,?_⟩⟩⟩
  intro y hy
  have hyr : ‖y‖<(r : ℝ) := by
    rw [Metric.eball_coe] at hy
    simpa using hy
  have hyR : ‖y‖<R := hyr.trans hrR
  have hyC : C*‖y‖<1 := by nlinarith [(lt_div_iff₀ hC).mp hrC]
  have hseg (t : ℝ) (ht : t∈Icc 0 1) : a+t•y∈Metric.ball a R := by
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hyR
  have hdiff (n : ℕ) (t : ℝ) (ht : t∈Icc 0 1) : ContDiffAt ℝ (n+1) f (a+t•y) :=
    ((hf _ (hseg t ht)).contDiffAt (Metric.isOpen_ball.mem_nhds (hseg t ht))).of_le (by exact_mod_cast (show (↑n+1 : ℕ∞)≤⊤ from le_top))
  have he (n : ℕ) :
      ‖f (a+y)-∑ k∈Finset.range (n+1), p k (fun _ => y)‖≤
        M*((n+1 : ℕ) : ℝ)*(C*‖y‖)^(n+1) := by
    rw [map_add_eq_sum_add_integral_iteratedFDeriv (hdiff n)]
    simp only [p,smul_apply,add_sub_cancel_left]
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    have hi : ‖∫ t in (0:ℝ)..1, (1-t)^n •
        iteratedFDeriv ℝ (n+1) f (a+t•y) (fun _ => y)‖≤
        M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1)) ?_).trans (by simp)
      intro t ht
      have ht' : t∈Icc (0:ℝ) 1 := by
        simp only [uIoc_of_le zero_le_one,mem_Ioc] at ht
        exact ⟨ht.1.le,ht.2⟩
      rw [norm_smul,Real.norm_of_nonneg (pow_nonneg (by linarith [ht'.2]) _)]
      calc
          _ ≤ 1*(‖iteratedFDeriv ℝ (n+1) f (a+t•y)‖*‖y‖^(n+1)) :=
            mul_le_mul (pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1]))
              (by simpa using (iteratedFDeriv ℝ (n+1) f (a+t•y)).le_opNorm (fun _ => y))
              (norm_nonneg _) (by positivity)
          _ ≤ M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb (n+1) _ (hseg t ht')) (by positivity : 0≤‖y‖^(n+1))
    calc
      _ ≤ (n.factorial : ℝ)⁻¹*(M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1)) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by
        rw [Nat.factorial_succ,Nat.cast_mul,mul_pow]
        have hn : (n.factorial : ℝ)≠0 := by positivity
        field_simp
  have ht : Tendsto (fun n : ℕ => M*((n+1 : ℕ) : ℝ)*(C*‖y‖)^(n+1)) atTop (𝓝 0) := by
    have hh := (tendsto_self_mul_const_pow_of_lt_one (show 0≤C*‖y‖ by positivity) hyC).comp
      (tendsto_add_atTop_nat 1)
    simpa only [mul_zero,mul_assoc,Function.comp_apply] using hh.const_mul M
  have hlim : Tendsto (fun n : ℕ => ∑ k∈Finset.range (n+1), p k (fun _ => y)) atTop (𝓝 (f (a+y))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp_rw [norm_sub_rev]
    exact squeeze_zero (fun _ => norm_nonneg _) he ht
  apply (hasSum_iff_tendsto_nat_of_summable_norm ?_).mpr
  · exact (tendsto_add_atTop_iff_nat 1).mp hlim
  · apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_geometric_of_lt_one (show 0≤C*‖y‖ by positivity) hyC).mul_left M)
    calc
      ‖p n (fun _ => y)‖≤‖p n‖*‖y‖^n := by simpa using (p n).le_opNorm (fun _ => y)
      _≤M*C^n*‖y‖^n := mul_le_mul_of_nonneg_right (hp n) (by positivity)
      _=M*(C*‖y‖)^n := by rw [mul_pow]; ring

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AnalyticNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter MeasureTheory Topology

section LocalNull
variable {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] (μ : Measure E)

lemma measure_inter_zero_of_local {U Z : Set E}
    (h : ∀ x ∈ U, ∃ V : Set E, x ∈ V ∧ IsOpen V ∧ μ (V ∩ Z) = 0) :
    μ (U ∩ Z) = 0 := by
  choose V hmem hopen hnull using (fun x : U => h x x.property)
  obtain ⟨I,hIc,hcov⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    V hopen (by intro x hx; exact mem_iUnion.mpr ⟨⟨x,hx⟩,hmem ⟨x,hx⟩⟩)
  apply measure_mono_null (t := ⋃ x ∈ I, V x ∩ Z)
  · intro x hx
    rcases mem_iUnion₂.mp (hcov hx.1) with ⟨y,hy,hxy⟩
    exact mem_iUnion₂.mpr ⟨y,hy,hxy,hx.2⟩
  · exact (measure_biUnion_null_iff hIc).mpr (fun x _ => hnull x)
end LocalNull

lemma analyticNull_real : AnalyticNullProperty ℝ volume := by
  intro U f hU hc hf ⟨x,hx,hfx⟩
  have hd : IsDiscrete (f ⁻¹' {0} ∩ U) := isDiscrete_of_codiscreteWithin
    (by simpa only [preimage_compl] using
      hf.preimage_zero_mem_codiscreteWithin hfx hx ⟨⟨x,hx⟩,hc⟩)
  rw [inter_comm]
  exact ((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd).measure_zero volume

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]

omit [SecondCountableTopology E] in
lemma analytic_zero_measurable {U : Set E} {f : E → ℝ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℝ f U) :
    MeasurableSet (U ∩ f ⁻¹' {0}) := by
  have ho := hf.continuousOn.isOpen_inter_preimage hU (isClosed_singleton.isOpen_compl : IsOpen ({0}ᶜ : Set ℝ))
  convert hU.measurableSet.diff ho.measurableSet using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,Set.mem_sdiff,mem_compl_iff]
  tauto

omit [SecondCountableTopology E] in
lemma analytic_null_rectangle (μ : Measure E) (ν : Measure F) [SFinite ν]
    (hE : AnalyticNullProperty E μ) (hF : AnalyticNullProperty F ν)
    {U : Set E} {V : Set F} {f : E × F → ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hcU : IsPreconnected U) (hcV : IsPreconnected V)
    (hf : AnalyticOnNhd ℝ f (U ×ˢ V)) (hx : ∃ x ∈ U ×ˢ V, f x ≠ 0) :
    μ.prod ν ((U ×ˢ V) ∩ f ⁻¹' {0}) = 0 := by
  obtain ⟨⟨x₀,y₀⟩,hxy,hfxy⟩ := hx
  have ha : AnalyticOnNhd ℝ (fun x => f (x,y₀)) U := by
    intro x hx
    have hg : AnalyticAt ℝ (fun t : E => (t,y₀)) x := analyticAt_id.prod analyticAt_const
    exact (hf (x,y₀) ⟨hx,hxy.2⟩).comp (f := fun t : E => (t,y₀)) hg
  have hn := hE U (fun x => f (x,y₀)) hU hcU ha ⟨x₀,hxy.1,hfxy⟩
  apply Measure.measure_prod_null_of_ae_null (analytic_zero_measurable (hU.prod hV) hf)
  filter_upwards [compl_mem_ae_iff.mpr hn] with x hx
  by_cases hxU : x ∈ U
  · have hfx : f (x,y₀) ≠ 0 := by simpa [hxU] using hx
    have hb : AnalyticOnNhd ℝ (fun y => f (x,y)) V := by
      intro y hy
      have hg : AnalyticAt ℝ (fun t : F => (x,t)) y := analyticAt_const.prod analyticAt_id
      exact (hf (x,y) ⟨hxU,hy⟩).comp (f := fun t : F => (x,t)) hg
    change ν (Prod.mk x ⁻¹' ((U ×ˢ V) ∩ f ⁻¹' {0})) = 0
    have he : Prod.mk x ⁻¹' ((U ×ˢ V) ∩ f ⁻¹' {0}) =
        V ∩ (fun y => f (x,y)) ⁻¹' {0} := by ext y; simp [hxU]
    rw [he]
    exact hF V (fun y => f (x,y)) hV hcV hb ⟨y₀,hxy.2,hfx⟩
  · simp [hxU]

lemma analyticNull_prod (μ : Measure E) (ν : Measure F) [SFinite ν]
    (hE : AnalyticNullProperty E μ) (hF : AnalyticNullProperty F ν) :
    AnalyticNullProperty (E × F) (μ.prod ν) := by
  intro U f hU hc hf ⟨x₀,hx₀,hfx₀⟩
  apply measure_inter_zero_of_local
  intro p hp
  obtain ⟨ε,hε,hsub⟩ := Metric.isOpen_iff.mp hU p hp
  let V := Metric.ball p.1 ε ×ˢ Metric.ball p.2 ε
  have hVm : p ∈ V := ⟨Metric.mem_ball_self hε,Metric.mem_ball_self hε⟩
  have hVo : IsOpen V := Metric.isOpen_ball.prod Metric.isOpen_ball
  have hVU : V ⊆ U := by
    intro q hq
    apply hsub
    rw [Metric.mem_ball,Prod.dist_eq]
    exact max_lt hq.1 hq.2
  have hne : ∃ x ∈ V, f x ≠ 0 := by
    by_contra! hn
    have he : f =ᶠ[𝓝 p] 0 := by
      filter_upwards [hVo.mem_nhds hVm] with x hx
      exact hn x hx
    exact hfx₀ (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hp he hx₀)
  refine ⟨V,hVm,hVo,?_⟩
  exact analytic_null_rectangle μ ν hE hF Metric.isOpen_ball Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (convex_ball _ _).isPreconnected (hf.mono hVU) hne

end ScalarConductivity



namespace ScalarConductivity
open Set Filter MeasureTheory Topology

section Transfer
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]

omit [BorelSpace E] [SecondCountableTopology E] [SecondCountableTopology F] in
lemma analyticNull_of_equiv (μ : Measure E) (ν : Measure F) (e : E ≃L[ℝ] F)
    (he : MeasurePreserving e μ ν) (hF : AnalyticNullProperty F ν) :
    AnalyticNullProperty E μ := by
  intro U f hU hc hf ⟨x,hx,hfx⟩
  let V := e '' U
  have hVo : IsOpen V := e.toHomeomorph.isOpenMap _ hU
  have hg : AnalyticOnNhd ℝ (fun y => f (e.symm y)) V := by
    rintro y ⟨z,hz,rfl⟩
    apply (hf z hz).comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply z)
  have hn := hF V (fun y => f (e.symm y)) hVo
    (hc.image e e.continuous.continuousOn) hg ⟨e x,mem_image_of_mem _ hx,by simpa using hfx⟩
  rw [←he.measure_preimage (analytic_zero_measurable hVo hg).nullMeasurableSet] at hn
  have hs : U ∩ f ⁻¹' {0} = e ⁻¹' (V ∩ (fun y => f (e.symm y)) ⁻¹' {0}) := by
    ext z
    simp [V]
  rw [hs]
  exact hn
end Transfer

lemma splitFinCLE_measurePreserving (n : ℕ) :
    MeasurePreserving (splitFinCLE n) volume volume :=
  volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0

theorem analyticNull_fin (n : ℕ) : AnalyticNullProperty (Fin n → ℝ) volume := by
  induction n with
  | zero =>
    intro U f hU hc hf ⟨x,hx,hfx⟩
    have h : U ∩ f ⁻¹' {0} = ∅ := by
      apply eq_empty_of_forall_notMem
      intro y hy
      exact hfx (by simpa only [Subsingleton.elim y x, mem_preimage, mem_singleton_iff] using hy.2)
    rw [h,measure_empty]
  | succ n ih =>
    exact analyticNull_of_equiv volume volume (splitFinCLE n) (splitFinCLE_measurePreserving n)
      (analyticNull_prod volume volume analyticNull_real ih)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AnalyticNullEuclidean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma analytic_directional_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {U : Set E} (hf : AnalyticOnNhd ℝ f U) (w : E) :
    AnalyticOnNhd ℝ (fun x => fderiv ℝ f x w) U :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp_analyticOnNhd hf.fderiv

lemma analytic_gradient_minor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E → ℝ} {U : Set E} (hu : AnalyticOnNhd ℝ u U)
    (hv : AnalyticOnNhd ℝ v U) (p q : E) :
    AnalyticOnNhd ℝ (fun x => fderiv ℝ u x p*fderiv ℝ v x q-
      fderiv ℝ u x q*fderiv ℝ v x p) U :=
  ((analytic_directional_fderiv hu p).mul (analytic_directional_fderiv hv q)).sub
    ((analytic_directional_fderiv hu q).mul (analytic_directional_fderiv hv p))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

lemma faceRayDensity_pos' {w : ℝ} (hw : 0<w) (j : Fin 4) (b : ℝ) :
    0<faceRayDensity w j b := by
  fin_cases j <;> dsimp [faceRayDensity] <;> positivity

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_AxialExtension
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma axialZeroExtension_eventually_self {d e : ℝ} {f : Coord3 → E} {x : Coord3}
    (hx : d+e/2<x 0) : axialZeroExtension d e f=ᶠ[𝓝 x] f := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hx] with y hy
  exact ite_eq_left hy

omit [NormedSpace ℝ E] in
lemma axialZeroExtension_eventually_zero {d e : ℝ} (he : 0<e) {f : Coord3 → E}
    (hf : ∀ x,x 0∈Icc d (d+e) → f x=0) {x : Coord3} (hx : x 0<d+e) :
    axialZeroExtension d e f=ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [(isOpen_lt (continuous_apply 0) continuous_const).mem_nhds hx] with y hy
  dsimp only [axialZeroExtension]
  split_ifs with hh
  · exact hf y ⟨by linarith only [he,hh],hy.le⟩
  · rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_TorusEndingCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma torusEndingCorrection_initial_zero {d e : ℝ} (he : 0<e)
    {v f : Coord3 → ℝ} (hz : ∀ x,x 0∈Ioo d (d+e) → v x=f x)
    {x : Coord3} (hx : x 0<d+3*e/4) :
    torusEndingCorrection d e v f=ᶠ[𝓝 x] (fun _ => 0) := by
  apply axialZeroExtension_eventually_zero (by linarith : 0<e/2) _ (by linarith)
  intro y hy
  change v y-f y=0
  exact sub_eq_zero.mpr (hz y ⟨by linarith [hy.1],by linarith [hy.2]⟩)

lemma torusEndingCorrection_terminal {d e : ℝ} {v f : Coord3 → ℝ}
    {x : Coord3} (hx : d+e/2<x 0) :
    torusEndingCorrection d e v f=ᶠ[𝓝 x] (v-f) :=
  axialZeroExtension_eventually_self (by linarith)

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma torusInitialPair_eq (s : Fin 3 → ℝ) (f : Fin 2 → TorusL2) (x : Coord3) :
    torusInitialPair s f x=![x 0+torusRealContinuation s (f 0) x,torusRealContinuation s (f 1) x] := by
  ext j
  fin_cases j <;> simp [torusInitialPair,torusAffineField,normalizedSlope]

namespace TorusEndingData
variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (z : TorusEndingData s f)

lemma initial_field (x : Coord3) (hx : x 0∈Ioo z.d (z.d+z.e)) :
    z.w.v x=torusInitialPair s f x := by
  rw [z.initial_v x ⟨hx.1.le,hx.2.le⟩,torusInitialPair_eq]

end TorusEndingData
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusSpectralContinuation
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma mFourierCoeff_Lp_add (f g : TorusL2) (h : Fin 2 → ℤ) :
    mFourierCoeff (f+g) h=mFourierCoeff f h+mFourierCoeff g h := by
  simp only [←mFourierBasis_repr,map_add,lp.coeFn_add,Pi.add_apply]

lemma mFourierCoeff_Lp_neg (f : TorusL2) (h : Fin 2 → ℤ) :
    mFourierCoeff (-f) h= -mFourierCoeff f h := by
  simp only [←mFourierBasis_repr,map_neg,lp.coeFn_neg,Pi.neg_apply]

lemma torusPoissonContinuous_add {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {t : ℝ} (ht : 0<t) (f g : TorusL2) :
    torusPoissonContinuous s t (f+g)=torusPoissonContinuous s t f+torusPoissonContinuous s t g := by
  unfold torusPoissonContinuous
  simp only [mFourierCoeff_Lp_add,mul_add]
  calc
    _ = ∑' h, (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h) • mFourier h+
        ((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff g h) • mFourier h) := by
      apply tsum_congr
      intro h
      exact _root_.add_smul (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h))
        (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff g h)) (mFourier h)
    _ = _ := (poisson_series_norm_summable hs ht f).of_norm.tsum_add
      (poisson_series_norm_summable hs ht g).of_norm

lemma torusPoissonContinuous_neg (s : Fin 3 → ℝ) (t : ℝ) (f : TorusL2) :
    torusPoissonContinuous s t (-f)= -torusPoissonContinuous s t f := by
  unfold torusPoissonContinuous
  simp only [mFourierCoeff_Lp_neg,mul_neg]
  calc
    _ = ∑' h, - (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h) • mFourier h) := by
      apply tsum_congr
      intro h
      exact _root_.neg_smul (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h)) (mFourier h)
    _ = _ := tsum_neg

lemma torusRealContinuation_add {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f g : TorusL2) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (f+g) x=torusRealContinuation s f x+torusRealContinuation s g x := by
  simp only [torusRealContinuation,torusPoissonContinuous_add hs hx,
    ContinuousMap.add_apply,Complex.add_re]

lemma torusRealContinuation_neg (s : Fin 3 → ℝ) (f : TorusL2) (x : Coord3) :
    torusRealContinuation s (-f) x= -torusRealContinuation s f x := by
  simp only [torusRealContinuation,torusPoissonContinuous_neg,ContinuousMap.neg_apply,Complex.neg_re]

lemma torusRealContinuation_sub {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f g : TorusL2) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (f-g) x=torusRealContinuation s f x-torusRealContinuation s g x := by
  simp only [sub_eq_add_neg,torusRealContinuation_add hs f (-g) hx,torusRealContinuation_neg]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_BranchOutputNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

variable {E : Type*} [AddCommGroup E]

variable [Module ℝ E]

lemma branchNormalize_basis_slopes (i : Fin 3) :
    branchNormalize i (fun j => centralBasisSlopes j i)=normalizedSlope := by
  ext j
  fin_cases i <;> fin_cases j <;> norm_num [branchNormalize,centralBasisSlopes,normalizedSlope]

lemma branchNormalize_normalized_slope (i : Fin 3) :
    branchNormalize i normalizedSlope=(fun j => centralBasisSlopes j i) := by
  rw [←branchNormalize_basis_slopes i,branchNormalize_involutive i]

lemma branchNormalize_affineField {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (i : Fin 3) (κ : Fin 2 → ℝ) (f : Fin 2 → TorusL2) {x : Coord3} (hx : 0<x 0) :
    branchNormalize i (fun j => torusAffineField s (κ j) (f j) x)=
      fun j => torusAffineField s (branchNormalize i κ j) (branchNormalize i f j) x := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [branchNormalize,torusAffineField,torusRealContinuation_neg,
      torusRealContinuation_sub hs _ _ hx] <;> ring

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_BranchFiniteEnding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma branchFinitePair_v {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) (x : Coord3) :
    (branchFinitePair i z).v x=branchNormalize i (z.w.v x) := by
  simp [branchFinitePair]

lemma branchFinitePair_initial {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {f : Fin 2 → TorusL2} (i : Fin 3) (z : TorusEndingData s (branchNormalize i f))
    (x : Coord3) (hx : x 0∈Ioo z.d (z.d+z.e)) :
    (branchFinitePair i z).v x=fun j => torusAffineField s (centralBasisSlopes j i) (f j) x := by
  rw [branchFinitePair_v,z.initial_field x hx]
  change branchNormalize i (fun j => torusAffineField s (normalizedSlope j)
    (branchNormalize i f j) x)=_
  rw [branchNormalize_affineField hs i normalizedSlope (branchNormalize i f) (z.d_pos.trans hx.1),
    branchNormalize_normalized_slope,branchNormalize_involutive]

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_FlatEndingSplice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i f))

lemma branchSplicedField_initial
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {x : Coord3} (hx : x 0<z.d+3*z.e/4) :
    branchSplicedField i z j=ᶠ[𝓝 x] torusAffineField s (centralBasisSlopes j i) (f j) := by
  filter_upwards [torusEndingCorrection_initial_zero z.e_pos
    (fun y hy => congrFun (branchFinitePair_initial hs i z y hy) j) hx] with y hy
  change _+torusEndingCorrection _ _ _ _ y=_
  rw [hy,add_zero]

lemma branchSplicedField_final (j : Fin 2) {x : Coord3} (hx : z.d+z.e/2<x 0) :
    branchSplicedField i z j=ᶠ[𝓝 x] (fun y => (branchFinitePair i z).v y j) := by
  filter_upwards [torusEndingCorrection_terminal
    (v:=fun y => (branchFinitePair i z).v y j)
    (f:=torusAffineField s (centralBasisSlopes j i) (f j)) hx] with y hy
  change _+torusEndingCorrection _ _ _ _ y=_
  rw [hy]
  change torusAffineField s (centralBasisSlopes j i) (f j) y+
    ((branchFinitePair i z).v y j-torusAffineField s (centralBasisSlopes j i) (f j) y)=_
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FacePasting
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix

variable {E : Type*}

lemma sourceFacePasteList_local (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (y : Coord3)
    (hy : ∃ k∈ks,y∈sourceFlatPatch k.1 k.2) :
    ∃ k∈ks,y∈sourceFlatPatch k.1 k.2 ∧ sourceFacePasteList B v ks y=B k.1 k.2 y := by
  classical
  induction ks with
  | nil => simp at hy
  | cons k ks ih =>
    by_cases hk : y∈sourceFlatPatch k.1 k.2
    · exact ⟨k,List.mem_cons_self,hk,by rw [sourceFacePasteList_cons,ite_eq_left hk]⟩
    · obtain ⟨l,hl,hly⟩ := hy
      have hl' : l∈ks := (List.mem_cons.mp hl).resolve_left (by rintro rfl; exact hk hly)
      obtain ⟨l,hl,hly,he⟩ := ih ⟨l,hl',hly⟩
      exact ⟨l,List.mem_cons_of_mem _ hl,hly,by rw [sourceFacePasteList_cons,ite_eq_right hk,he]⟩

lemma sourceFacePasteList_open (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (hk : (i,j)∈ks) :
    sourceFacePasteList B v ks (sourceCollarPiece i j x)=B i j (sourceCollarPiece i j x) := by
  obtain ⟨k,_,hy,he⟩ := sourceFacePasteList_local B v ks _
    ⟨(i,j),hk,⟨x,sourceCollarOpenBox_subset hx,rfl⟩⟩
  obtain ⟨z,hz,hze⟩ := hy
  obtain ⟨hi,hj⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx hz hze.symm
  simpa only [←hi,←hj] using he

lemma sourceFacePaste_open (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    sourceFacePaste B v (sourceCollarPiece i j x)=B i j (sourceCollarPiece i j x) :=
  sourceFacePasteList_open B v _ i j hx (by simp)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_NonzeroJacobianAE
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma ae_comp_of_nonzero_jacobian {f : Coord3 → Coord3}
    {D : Coord3 → Coord3 →L[ℝ] Coord3}
    (hf : ∀ x,HasFDerivAt f (D x) x) (hi : Function.Injective f)
    (hm : Measurable (fun x => ENNReal.ofReal |(D x).det|))
    (hn : ∀ x,(D x).det≠0) {P : Coord3 → Prop} (hP : ∀ᵐ y ∂volume,P y) :
    ∀ᵐ x ∂volume,P (f x) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have he := map_withDensity_abs_det_fderiv_eq_addHaar (μ:=volume)
    (s:=univ) MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hf x).hasFDerivWithinAt) hi.injOn
  simp only [Measure.restrict_univ] at he
  have hp : ∀ᵐ y ∂Measure.map f (volume.withDensity (fun x => ENNReal.ofReal |(D x).det|)),P y := by
    rw [he]
    exact ae_restrict_of_ae hP
  have h := ae_of_ae_map hc.measurable.aemeasurable hp
  rw [ae_withDensity_iff hm] at h
  filter_upwards [h] with x hx
  exact hx (by simpa only [ne_eq,ENNReal.ofReal_eq_zero,abs_nonpos_iff] using hn x)

lemma faceRayAngle_injective {w : ℝ} (hw : 0<w) (i : Fin 4) :
    Function.Injective (faceRayAngle w i) :=
  (strictMono_of_hasDerivAt_pos (hasDerivAt_faceRayAngle w i)
    (faceRayDensity_pos' hw i)).injective

lemma sourceFaceAngles_injective (i j : Fin 4) : Function.Injective (sourceFaceAngles i j) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [sourceFaceAngles,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at h0 h1 h2
  have hπ : 2*Real.pi≠0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have h1' := faceRayAngle_injective (by norm_num : (0:ℝ)<1) i (mul_left_cancel₀ hπ h1)
  have h2' := faceRayAngle_injective (by norm_num [sourceRadialWidth,sourceHole] : (0:ℝ) < sourceRadialWidth)
    j (mul_left_cancel₀ hπ h2)
  ext k
  fin_cases k <;> assumption

lemma sourceFaceAngles_ae {P : Coord3 → Prop} (hP : ∀ᵐ y ∂volume,P y) (i j : Fin 4) :
    ∀ᵐ x ∂volume,P (sourceFaceAngles i j x) := by
  apply ae_comp_of_nonzero_jacobian (sourceFaceAngles_hasFDeriv i j)
    (sourceFaceAngles_injective i j) _ _ hP
  · change Measurable (fun x : Coord3 => ENNReal.ofReal |(Matrix.toLin' (sourceFaceAngleMatrix i j x)).det|)
    simp only [LinearMap.det_toLin',sourceFaceAngleMatrix_det]
    exact (((continuous_const.mul ((continuous_faceRayDensity 1 i).comp (continuous_apply 1))).mul
      ((continuous_faceRayDensity sourceRadialWidth j).comp (continuous_apply 2))).abs.measurable.ennreal_ofReal)
  · intro x
    change (Matrix.toLin' (sourceFaceAngleMatrix i j x)).det≠0
    rw [LinearMap.det_toLin']
    rw [sourceFaceAngleMatrix_det]
    exact (mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one angularArea_ge_one)
      (faceRayDensity_pos' (by norm_num) i (x 1)))
      (faceRayDensity_pos' (by norm_num [sourceRadialWidth,sourceHole]) j (x 2))).ne'

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFaceSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceExtendedBox_mono {l r l' r' : ℝ} (hl : l'≤l) (hr : r ≤ r') :
    sourceExtendedBox l r ⊆ sourceExtendedBox l' r' := by
  intro x hx
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,ha,hb⟩

lemma sourceCollarPieces_aedisjoint {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    Pairwise (fun k m : Fin 4 × Fin 4 => AEDisjoint volume
      (sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r)
      (sourceCollarPiece m.1 m.2 '' sourceExtendedBox l r)) := by
  intro k m hkm
  have hn : ∀ᵐ y : Fin 3 → ℝ, y∉
      (sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r) ∩
      (sourceCollarPiece m.1 m.2 '' sourceExtendedBox l r) := by
    filter_upwards [sourceCollar_open_charts_ae] with y hy hm
    obtain ⟨⟨z,hz,hzy⟩,w,hw,hwy⟩ := hm
    have hyb := sourceCollarClosedPiece_subset (l:=-(1:ℝ)/100) (r:=1/100)
      le_rfl le_rfl k.1 k.2 ⟨z,sourceExtendedBox_mono hl hr hz,hzy⟩
    obtain ⟨i,j,x,hx,hxy⟩ := hy hyb
    obtain ⟨hik,hjk⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx
      (sourceExtendedBox_mono hl hr hz) (hxy.trans hzy.symm)
    obtain ⟨him,hjm⟩ := sourceCollarPiece_open_unique i j m.1 m.2 hx
      (sourceExtendedBox_mono hl hr hw) (hxy.trans hwy.symm)
    exact hkm (Prod.ext (hik.symm.trans him) (hjk.symm.trans hjm))
  simpa only [AEDisjoint,ae_iff,not_not,Set.ofPred_mem_eq] using hn

theorem sourceClosedCollarBand_measure_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    volume.restrict (sourceClosedCollarBand l r)=
      ∑ i : Fin 4,∑ j : Fin 4,
        volume.restrict (sourceCollarPiece i j '' sourceExtendedBox l r) := by
  rw [sourceClosedCollarBand_eq l r hl hr]
  have he : (⋃ i : Fin 4,⋃ j : Fin 4,sourceCollarPiece i j '' sourceExtendedBox l r)=
      ⋃ k : Fin 4 × Fin 4,sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r := by
    ext x
    simp
  rw [he,Measure.restrict_iUnion_ae (sourceCollarPieces_aedisjoint hl hr)
    (fun k => (sourceCollarClosedPiece_measurable l r k.1 k.2).nullMeasurableSet),
    Measure.sum_fintype,Fintype.sum_prod_type]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalNullTransport
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma flatEndCoordinates_ae {a : ℝ} (ha : a≠0) (b : ℝ)
    {P : Coord3 → Prop} (hP : ∀ᵐ y ∂volume,P y) :
    ∀ᵐ x ∂volume,P (flatEndCoordinates a b x) := by
  apply ae_comp_of_nonzero_jacobian (endAxialAffine_hasFDeriv a b) _ _ _ hP
  · intro x y h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [endAxialAffine,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at h0 h1 h2
    have h0' : x 0=y 0 := by linarith [mul_left_cancel₀ ha h0]
    ext k
    fin_cases k <;> assumption
  · exact measurable_const
  · intro x
    change (Matrix.toLin' (endAxialMatrix a)).det≠0
    simpa [LinearMap.det_toLin',endAxialMatrix,Matrix.det_diagonal,Fin.prod_univ_succ] using ha

lemma ae_image_of_differentiable {f : Coord3 → Coord3} {S : Set Coord3}
    (hS : MeasurableSet S) (hI : MeasurableSet (f '' S)) (hf : DifferentiableOn ℝ f S) {P : Coord3 → Prop}
    (hP : ∀ᵐ x ∂volume.restrict S,P (f x)) :
    ∀ᵐ y ∂volume.restrict (f '' S),P y := by
  have hn : volume {x | x∈S ∧ ¬ P (f x)}=0 := by
    rw [ae_restrict_iff' hS,ae_iff] at hP
    simpa using hP
  have hn' := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (hf.mono (show {x | x∈S ∧ ¬ P (f x)}⊆S from fun x hx => hx.1)) hn
  rw [ae_iff,Measure.restrict_apply' hI]
  apply le_antisymm _ bot_le
  have he : {y | ¬P y} ∩ f '' S ⊆ f '' {x | x∈S ∧ ¬P (f x)} := by
    rintro y ⟨hy,x,hx,rfl⟩
    exact ⟨x,⟨hx,hy⟩,rfl⟩
  exact (measure_mono he).trans hn'.le

lemma sourceClosedCollarBand_ae_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {P : Coord3 → Prop}
    (hP : ∀ i j : Fin 4,∀ᵐ x ∂volume.restrict (sourceExtendedBox l r),
      P (sourceCollarPiece i j x)) :
    ∀ᵐ y ∂volume.restrict (sourceClosedCollarBand l r),P y := by
  rw [sourceClosedCollarBand_measure_faces hl hr]
  simp only [ae_finsetSum_measure_iff,Finset.mem_univ,true_implies]
  intro i j
  exact ae_image_of_differentiable measurableSet_Icc (sourceCollarClosedPiece_measurable l r i j)
    (fun x _ => (sourceCollarPiece_hasFDeriv i j x).differentiableAt.differentiableWithinAt)
    (hP i j)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_FiniteEndPhysicalSmoothTensor
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma contDiffAt_mat3_det {A : Coord3 → Mat3} {x : Coord3} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) : ContDiffAt ℝ n (fun y => (A y).det) x := by
  simp_rw [Matrix.det_fin_three]
  have hc (i j : Fin 3) := contDiffAt_pi.mp (contDiffAt_pi.mp hA i) j
  fun_prop

lemma contDiffAt_mat3_adjugate {A : Coord3 → Mat3} {x : Coord3} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) : ContDiffAt ℝ n (fun y => (A y).adjugate) x := by
  simp_rw [Matrix.adjugate_fin_three]
  have hc (i j : Fin 3) := contDiffAt_pi.mp (contDiffAt_pi.mp hA i) j
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> norm_num only [Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons] <;> fun_prop

lemma contDiffAt_mat3_inv {A : Coord3 → Mat3} {x : Coord3} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) (hd : (A x).det≠0) :
    ContDiffAt ℝ n (fun y => (A y)⁻¹) x := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv']
  exact ((contDiffAt_mat3_det hA).inv hd).smul (contDiffAt_mat3_adjugate hA)

lemma contDiffAt_mat3_transpose {A : Coord3 → Mat3} {x : Coord3} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) : ContDiffAt ℝ n (fun y => (A y)ᵀ) x := by
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    contDiffAt_pi.mp (contDiffAt_pi.mp hA j) i))

lemma contDiffAt_mat3_mul {A B : Coord3 → Mat3} {x : Coord3} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) (hB : ContDiffAt ℝ n B x) :
    ContDiffAt ℝ n (fun y => A y*B y) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum (fun k _ => (contDiffAt_pi.mp (contDiffAt_pi.mp hA i) k).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hB k) j))

lemma contDiff_faceRayAngle (w : ℝ) (j : Fin 4) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (faceRayAngle w j) := by
  have h1 : ContDiff ℝ (↑(⊤:ℕ∞)) (fun b : ℝ => Real.arctan (b/w)) :=
    Real.contDiff_arctan.comp (contDiff_id.div_const w)
  have h2 : ContDiff ℝ (↑(⊤:ℕ∞)) (fun b : ℝ => Real.arctan (w*b)) :=
    Real.contDiff_arctan.comp (contDiff_const.mul contDiff_id)
  unfold faceRayAngle
  fin_cases j <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> fun_prop

lemma contDiff_faceRayDensity (w : ℝ) (j : Fin 4) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (faceRayDensity w j) := by
  have h1 : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : ℝ => (1+(x/w)^2)⁻¹) :=
    (contDiff_const.add ((contDiff_id.div_const w).pow 2)).inv (fun x => by positivity)
  have h2 : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : ℝ => (1+(w*x)^2)⁻¹) :=
    (contDiff_const.add ((contDiff_const.mul contDiff_id).pow 2)).inv (fun x => by positivity)
  unfold faceRayDensity
  fin_cases j <;> dsimp <;> simp only [div_eq_mul_inv,one_mul] <;> fun_prop

lemma contDiff_sourceFaceAngles (i j : Fin 4) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (sourceFaceAngles i j) := by
  apply contDiff_pi.mpr
  intro k
  fin_cases k
  · exact contDiff_apply _ _ _
  · exact contDiff_const.mul ((contDiff_faceRayAngle 1 i).comp (contDiff_apply _ _ 1))
  · exact contDiff_const.mul ((contDiff_faceRayAngle sourceRadialWidth j).comp (contDiff_apply _ _ 2))

lemma contDiff_sourceCollarJacobian (i j : Fin 4) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (sourceCollarJacobian i j) := by
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  fin_cases a <;> fin_cases b <;>
    simp only [sourceCollarJacobian, sourceCollarRadius, squareFace, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] <;> fun_prop

lemma contDiff_sourceFaceAngleMatrix (i j : Fin 4) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (sourceFaceAngleMatrix i j) := by
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  by_cases hab : a=b
  · subst b
    fin_cases a <;> simp only [sourceFaceAngleMatrix,Matrix.diagonal_apply_eq]
    · exact contDiff_const
    · exact contDiff_const.mul ((contDiff_faceRayDensity 1 i).comp (contDiff_apply _ _ 1))
    · exact contDiff_const.mul ((contDiff_faceRayDensity sourceRadialWidth j).comp (contDiff_apply _ _ 2))
  · simp only [sourceFaceAngleMatrix,Matrix.diagonal_apply_ne _ hab]
    exact contDiff_const

lemma contDiffAt_sourceCartesianGradientMatrix (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    ContDiffAt ℝ (↑(⊤:ℕ∞)) (sourceCartesianGradientMatrix i j) x := by
  have hi := contDiffAt_mat3_inv (contDiffAt_mat3_transpose (contDiff_sourceCollarJacobian i j).contDiffAt)
    (by rw [Matrix.det_transpose]; exact sourceCollarJacobian_extended_ne_zero i j hx)
  exact contDiffAt_mat3_mul hi (contDiff_sourceFaceAngleMatrix i j).contDiffAt

lemma contDiffAt_attachedCartesianMatrix (a : ℝ) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    ContDiffAt ℝ (↑(⊤:ℕ∞)) (attachedCartesianMatrix a i j) x :=
  contDiffAt_mat3_mul (contDiffAt_sourceCartesianGradientMatrix i j hx) contDiffAt_const

lemma contDiffAt_sourceFlatDensity (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    ContDiffAt ℝ (↑(⊤:ℕ∞)) (sourceFlatDensity i j) x := by
  exact (contDiffAt_mat3_det (contDiff_sourceFaceAngleMatrix i j).contDiffAt).div
    ((contDiffAt_mat3_det (contDiff_sourceCollarJacobian i j).contDiffAt).abs
      (sourceCollarJacobian_extended_ne_zero i j hx))
    (abs_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j hx))

lemma contDiffAt_attachedVariableTensor {K : Coord3 → Mat3} {x : Coord3}
    (hK : ContDiffAt ℝ (↑(⊤:ℕ∞)) K x) {a : ℝ} (ha : a≠0) (i j : Fin 4)
    (hx : x∈sourceCollarOpenBox) :
    ContDiffAt ℝ (↑(⊤:ℕ∞)) (attachedVariableTensor K a i j) x := by
  have hi := contDiffAt_mat3_inv (contDiffAt_attachedCartesianMatrix a i j (sourceCollarOpenBox_subset hx))
    (attachedCartesianMatrix_det_ne_zero ha i j (sourceCollarOpenBox_subset hx))
  exact (contDiffAt_const.mul (contDiffAt_sourceFlatDensity i j (sourceCollarOpenBox_subset hx))).smul
    (contDiffAt_mat3_mul (contDiffAt_mat3_mul (contDiffAt_mat3_transpose hi) hK) hi)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_VariableCollarTensor
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma variableCollarTensor_open (K : Coord3 → Mat3) (a b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    variableCollarTensor K a b (sourceCollarPiece i j x)=
      attachedVariableTensor (fun y => K (flatEndCoordinates a b (sourceFaceAngles i j y))) a i j x := by
  rw [variableCollarTensor,sourceFacePaste_open _ _ i j hx]
  simp only [variableFaceTensor,sourceCollarInverse_point i j hx]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FiniteEndPhysicalRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma TwoFieldRankRegular.smoothCoordinates {u : Coord3 → Fin 2 → ℝ}
    {O V : Set Coord3} (hO : IsOpen O) (hV : IsOpen V)
    (hu : ContDiffOn ℝ (↑(⊤:ℕ∞)) u O) (h : TwoFieldRankRegular u O)
    {g : Coord3 → Coord3} (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g V)
    (hm : MapsTo g V O) (hs : ∀ x∈V,Function.Surjective (fderiv ℝ g x)) :
    TwoFieldRankRegular (u ∘ g) V := by
  rcases h with h|h|⟨κ,hκ⟩
  · left
    intro x hx
    have hd := (hu.differentiableOn (by simp) (g x) (hm hx)).differentiableAt (hO.mem_nhds (hm hx))
    have hdg := (hg.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx)
    rw [(hd.hasFDerivAt.comp x hdg.hasFDerivAt).fderiv]
    exact gradientColumns_rank _ ((gradientColumns_surjective _ (h (g x) (hm hx))).comp (hs x hx))
  · right; left
    obtain ⟨v,l,κ,hv,hl,hd,he⟩ := h
    refine ⟨v ∘ g,l,κ,hv.comp hg hm,hl,?_,fun x hx j => he (g x) (hm hx) j⟩
    intro x hx hz
    have hxv := (hv.differentiableOn (by simp) (g x) (hm hx)).differentiableAt (hO.mem_nhds (hm hx))
    have hdg := (hg.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx)
    rw [(hxv.hasFDerivAt.comp x hdg.hasFDerivAt).fderiv] at hz
    apply hd (g x) (hm hx)
    ext y
    obtain ⟨z,rfl⟩ := hs x hx y
    exact congrArg (fun D : Coord3 →L[ℝ] ℝ => D z) hz
  · exact Or.inr (Or.inr ⟨κ,fun x hx => hκ (g x) (hm hx)⟩)

lemma sourceCollarInverse_contDiffAt (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) :
    ContDiffAt ℝ (↑(⊤:ℕ∞)) (sourceCollarInverse i j) (sourceCollarPiece i j x) := by
  let f' := sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)
  have hf := (sourceCollarPiece_contDiff i j).contDiffAt (x:=x)
  have hd : HasFDerivAt (sourceCollarPiece i j) (f' : Coord3 →L[ℝ] Coord3) x :=
    (sourceCollarPiece_hasStrictFDeriv i j x (sourceCollarOpenBox_subset hx)).hasFDerivAt
  have hn : (↑(⊤:ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hh := hf.to_localInverse hd hn
  apply hh.congr_of_eventuallyEq
  have he : sourceCollarInverse i j =ᶠ[𝓝 (sourceCollarPiece i j x)] hf.localInverse hd hn :=
    (hf.hasStrictFDerivAt' hd hn).localInverse_unique (sourceCollarInverse_eventually_left i j hx)
  exact he

lemma isOpen_sourceCollarOpenImage (i j : Fin 4) :
    IsOpen (sourceCollarPiece i j '' sourceCollarOpenBox) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x,hx,rfl⟩
  rw [←sourceCollarPiece_map_nhds i j hx]
  exact Filter.image_mem_map (isOpen_sourceCollarOpenBox.mem_nhds hx)

lemma sourceCollarInverse_contDiffOn (i j : Fin 4) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (sourceCollarInverse i j)
      (sourceCollarPiece i j '' sourceCollarOpenBox) := by
  rintro _ ⟨x,hx,rfl⟩
  exact (sourceCollarInverse_contDiffAt i j hx).contDiffWithinAt

lemma sourceCollarInverse_fderiv_surjective (i j : Fin 4) {y : Coord3}
    (hy : y∈sourceCollarPiece i j '' sourceCollarOpenBox) :
    Function.Surjective (fderiv ℝ (sourceCollarInverse i j) y) := by
  obtain ⟨x,hx,rfl⟩ := hy
  rw [(sourceCollarInverse_hasStrictFDeriv i j hx).hasFDerivAt.fderiv]
  exact (sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)).symm.surjective

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma variableCollarField_open (u : Coord3 → Fin 2 → ℝ) (a b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    variableCollarField u a b (sourceCollarPiece i j x)=
      u (flatEndCoordinates a b (sourceFaceAngles i j x)) := by
  rw [variableCollarField,sourceFacePaste_open _ _ i j hx]
  simp only [variableFaceField,sourceCollarInverse_point i j hx]

lemma flatEndCoordinates_fderiv_surjective {a : ℝ} (ha : a≠0) (b : ℝ) (x : Coord3) :
    Function.Surjective (fderiv ℝ (flatEndCoordinates a b) x) := by
  change Function.Surjective (fderiv ℝ (endAxialAffine a b) x)
  rw [(endAxialAffine_hasFDeriv a b x).fderiv]
  exact (LinearMap.equivOfDetNeZero (Matrix.toLin' (endAxialMatrix a)) (by
    simpa [LinearMap.det_toLin',endAxialMatrix,Matrix.det_diagonal,Fin.prod_univ_succ] using ha)).surjective

lemma sourceFaceAngles_fderiv_surjective (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) : Function.Surjective (fderiv ℝ (sourceFaceAngles i j) x) := by
  rw [(sourceFaceAngles_hasFDeriv i j x).fderiv]
  exact (LinearMap.equivOfDetNeZero (Matrix.toLin' (sourceFaceAngleMatrix i j x)) (by
    rw [LinearMap.det_toLin']; exact (sourceFaceAngleMatrix_det_pos i j (sourceCollarOpenBox_subset hx)).ne')).surjective

lemma variableCollarTensor_local_eq (K : Coord3 → Mat3) (a b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    variableCollarTensor K a b =ᶠ[𝓝 (sourceCollarPiece i j x)]
      (attachedVariableTensor (K ∘ flatEndCoordinates a b ∘ sourceFaceAngles i j) a i j ∘ sourceCollarInverse i j) := by
  change ∀ᶠ y in 𝓝 (sourceCollarPiece i j x), _ = _
  rw [←sourceCollarPiece_map_nhds i j hx,eventually_map]
  filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx] with y hy
  simpa only [Function.comp_def,sourceCollarInverse_point i j hy] using
    variableCollarTensor_open K a b i j hy

lemma variableCollarTensor_smooth_at {K : Coord3 → Mat3} {a : ℝ} (ha : a≠0) (b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox)
    (hK : ContDiffAt ℝ (↑(⊤:ℕ∞)) K (flatEndCoordinates a b (sourceFaceAngles i j x))) :
    ContDiffAt ℝ (↑(⊤:ℕ∞)) (variableCollarTensor K a b) (sourceCollarPiece i j x) := by
  have hk : ContDiffAt ℝ (↑(⊤:ℕ∞)) (K ∘ flatEndCoordinates a b ∘ sourceFaceAngles i j) x :=
    hK.comp x ((contDiff_flatEndCoordinates a b).contDiffAt.comp x
      (contDiff_sourceFaceAngles i j).contDiffAt)
  have ht : ContDiffAt ℝ (↑(⊤:ℕ∞))
      (attachedVariableTensor (K ∘ flatEndCoordinates a b ∘ sourceFaceAngles i j) a i j)
      (sourceCollarInverse i j (sourceCollarPiece i j x)) := by
    rw [sourceCollarInverse_point i j hx]
    exact contDiffAt_attachedVariableTensor hk ha i j hx
  exact (ht.comp _ (sourceCollarInverse_contDiffAt i j hx)).congr_of_eventuallyEq
    (variableCollarTensor_local_eq K a b i j hx)

theorem variableCollar_regular_at {u : Coord3 → Fin 2 → ℝ} {K : Coord3 → Mat3}
    (hS : ∀ x,(K x).IsSymm) {a : ℝ} (ha : a≠0) (b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) {U : Set Coord3}
    (hr : flatEndCoordinates a b (sourceFaceAngles i j x)∈
      regularRegion u (fun y => ⟨K y,hS y⟩) U) :
    sourceCollarPiece i j x∈regularRegion (variableCollarField u a b)
      (fun y => ⟨variableCollarTensor K a b y,variableCollarTensor_symm hS a b y⟩)
      (sourceCollarPiece i j '' sourceCollarOpenBox) := by
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp hr
  let V := sourceCollarPiece i j '' sourceCollarOpenBox
  let g : Coord3 → Coord3 := fun y => flatEndCoordinates a b (sourceFaceAngles i j (sourceCollarInverse i j y))
  have hV : IsOpen V := isOpen_sourceCollarOpenImage i j
  have hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g V :=
    (contDiff_flatEndCoordinates a b).comp_contDiffOn
      ((contDiff_sourceFaceAngles i j).comp_contDiffOn (sourceCollarInverse_contDiffOn i j))
  let W := V∩g ⁻¹' O
  have hW : IsOpen W := hg.continuousOn.isOpen_inter_preimage hV hO.1
  have hm : MapsTo g W O := fun _ hy => hy.2
  have hd : ∀ y∈W,Function.Surjective (fderiv ℝ g y) := by
    rintro y ⟨⟨z,hz,rfl⟩,_⟩
    have hinv := (sourceCollarInverse_contDiffAt i j hz).differentiableAt (by simp)
    have hang := (contDiff_sourceFaceAngles i j).differentiable (by simp)
    have hflat := (contDiff_flatEndCoordinates a b).differentiable (by simp)
    change Function.Surjective (fderiv ℝ (flatEndCoordinates a b ∘ (sourceFaceAngles i j ∘ sourceCollarInverse i j)) _)
    rw [fderiv_comp _ (hflat _) ((hang _).comp _ hinv),fderiv_comp _ (hang _) hinv]
    have hsur : Function.Surjective (fderiv ℝ (sourceFaceAngles i j)
        (sourceCollarInverse i j (sourceCollarPiece i j z))) := by
      simpa only [sourceCollarInverse_point i j hz] using sourceFaceAngles_fderiv_surjective i j hz
    exact (flatEndCoordinates_fderiv_surjective ha b _).comp
      (hsur.comp (sourceCollarInverse_fderiv_surjective i j ⟨z,hz,rfl⟩))
  have hB : ContDiffOn ℝ (↑(⊤:ℕ∞)) (variableCollarTensor K a b) W := by
    rintro y hy
    obtain ⟨z,hz,rfl⟩ := hy.1
    apply (variableCollarTensor_smooth_at ha b i j hz ?_).contDiffWithinAt
    have hgz : g (sourceCollarPiece i j z)=flatEndCoordinates a b (sourceFaceAngles i j z) := by
      simp only [g,sourceCollarInverse_point i j hz]
    simpa only [hgz] using (hO.2.2.1 _ hy.2).contDiffAt (hO.1.mem_nhds hy.2)
  have hp : RegularPatch (fun y => u (g y))
      (fun y => ⟨variableCollarTensor K a b y,variableCollarTensor_symm hS a b y⟩) W :=
    ⟨hW,hO.2.1.comp (hg.mono inter_subset_left) hm,hB,
      hO.2.2.2.smoothCoordinates hO.1 hW hO.2.1 (hg.mono inter_subset_left) hm hd⟩
  have hc : EqOn (variableCollarField u a b) (fun y => u (g y)) W := by
    rintro y ⟨⟨z,hz,rfl⟩,_⟩
    simpa only [g,sourceCollarInverse_point i j hz] using variableCollarField_open u a b i j hz
  refine mem_regularRegion_iff.mpr ⟨W,inter_subset_left,hp.congr hc (fun _ _ => rfl),?_⟩
  refine ⟨⟨x,hx,rfl⟩,?_⟩
  change g (sourceCollarPiece i j x)∈O
  simpa only [g,sourceCollarInverse_point i j hx] using hxO

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPatchCoordinates
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma TwoFieldRankRegular.comp {u : Coord3 → Fin 2 → ℝ} {O V : Set Coord3}
    (hO : IsOpen O) (hV : IsOpen V)
    (hu : ContDiffOn ℝ (↑(⊤:ℕ∞)) u O) (h : TwoFieldRankRegular u O)
    {P : Coord3 → Coord3} (hP : ContDiffOn ℝ (↑(⊤:ℕ∞)) P V)
    (hm : MapsTo P V O) (hd : ∀ x∈V,Function.Surjective (fderiv ℝ P x)) :
    TwoFieldRankRegular (fun x => u (P x)) V := by
  have hPd (x) (hx : x∈V) :=
    (hP.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx)
  rcases h with h|h|⟨κ,hκ⟩
  · left
    intro x hx
    have hud := (hu.differentiableOn (by simp) (P x) (hm hx)).differentiableAt
      (hO.mem_nhds (hm hx))
    change LinearIndependent ℝ (gradientColumns (fderiv ℝ (u ∘ P) x)).col
    rw [(hud.hasFDerivAt.comp x (hPd x hx).hasFDerivAt).fderiv]
    exact gradientColumns_rank _ ((gradientColumns_surjective _ (h (P x) (hm hx))).comp (hd x hx))
  · right; left
    obtain ⟨v,l,κ,hv,hl,hvd,he⟩ := h
    refine ⟨fun x => v (P x),l,κ,hv.comp hP hm,hl,?_,fun x hx j => he (P x) (hm hx) j⟩
    intro x hx hz
    have hvd' := (hv.differentiableOn (by simp) (P x) (hm hx)).differentiableAt
      (hO.mem_nhds (hm hx))
    change fderiv ℝ (v ∘ P) x=0 at hz
    rw [(hvd'.hasFDerivAt.comp x (hPd x hx).hasFDerivAt).fderiv] at hz
    apply hvd (P x) (hm hx)
    ext y
    obtain ⟨t,ht⟩ := hd x hx y
    have ht' := congrArg (fun D : Coord3 →L[ℝ] ℝ => D t) hz
    simpa only [ContinuousLinearMap.comp_apply,ht,_root_.zero_apply] using ht'
  · exact Or.inr (Or.inr ⟨κ,fun x hx => hκ (P x) (hm hx)⟩)

lemma RegularPatch.comp {u : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    {O V : Set Coord3} (h : RegularPatch u A O) (hV : IsOpen V)
    {P : Coord3 → Coord3} (hP : ContDiffOn ℝ (↑(⊤:ℕ∞)) P V)
    (hm : MapsTo P V O) (hd : ∀ x∈V,Function.Surjective (fderiv ℝ P x))
    (hB : ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun x => (B x).val) V) :
    RegularPatch (fun x => u (P x)) B V :=
  ⟨hV,h.2.1.comp hP hm,hB,h.2.2.2.comp h.1 hV h.2.1 hP hm hd⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFourierAnalytic
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory UnitAddTorus

lemma flatFourier_factorial_bound {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B δ : ℝ} (ha : ∀ h,|a h|≤B) (hδ : 0<δ)
    (n : ℕ) {x : Coord3} (hx : δ≤x 0) :
    ‖iteratedFDeriv ℝ n (flatFourier s a phase) x‖≤
      (B*(∑' h : Fin 2 → ℤ,exp (-(δ/2)*torusRate s h)))*
        (3/(δ/2))^n*(n.factorial : ℝ) := by
  have hB : 0≤B := (abs_nonneg (a 0)).trans (ha 0)
  have he := torusRate_exp_summable hs (by positivity : 0<δ/2)
  have hmode := (flatMode_derivative_summable hs n hδ).mul_left B
  have hb (h : Fin 2 → ℤ) :
      B*((torusRate s h+torusSize h)^n*exp (-δ*torusRate s h))≤
        (B*((3:ℝ)^n*((n.factorial : ℝ)/(δ/2)^n)))*exp (-(δ/2)*torusRate s h) := by
    have hl := torusRate_lower hs h
    have hlam : 0≤torusRate s h := sqrt_nonneg _
    calc
      _ ≤ B * ((3:ℝ)^n*(((n.factorial : ℝ)/(δ/2)^n)*exp (-(δ/2)*torusRate s h))) := by
        apply mul_le_mul_of_nonneg_left _ hB
        calc
          _≤(3*torusRate s h)^n*exp (-δ*torusRate s h) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (add_nonneg hlam (torusSize_nonneg h)) (by linarith) _) (exp_nonneg _)
          _=3^n*((torusRate s h)^n*exp (-δ*torusRate s h)) := by rw [mul_pow]; ring
          _≤3^n*(((n.factorial : ℝ)/(δ/2)^n)*exp (-(δ/2)*torusRate s h)) :=
            mul_le_mul_of_nonneg_left (pow_mul_exp_bound n hδ hlam) (by positivity)
      _ = _ := by ring
  calc
    _≤∑' h,B*((torusRate s h+torusSize h)^n*exp (-δ*torusRate s h)) :=
      flatFourier_iterated_norm hs ha hδ n hx
    _≤∑' h,(B*((3:ℝ)^n*((n.factorial : ℝ)/(δ/2)^n)))*exp (-(δ/2)*torusRate s h) :=
      hmode.tsum_le_tsum hb (he.mul_left _)
    _=_ := by
      rw [tsum_mul_left]
      generalize δ/2 = θ
      rw [div_pow]
      ring

lemma flatFourier_analytic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B) :
    AnalyticOnNhd ℝ (flatFourier s a phase) {x | 0<x 0} := by
  intro x hx
  change 0<x 0 at hx
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp
    ((axial_halfspace_open (x 0/2)).mem_nhds (by change x 0/2<x 0; linarith))
  have hB : 0≤B := (abs_nonneg (a 0)).trans (ha 0)
  apply analyticAt_of_factorial_bound hR
    (M:=B*(∑' h : Fin 2 → ℤ,exp (-(x 0/2/2)*torusRate s h)))
    (C:=3/(x 0/2/2)) (mul_nonneg hB (tsum_nonneg (fun _ => exp_nonneg _))) (by positivity)
  · exact (flatFourier_smooth hs ha).mono (fun y hy => by
      have h := hball hy
      change x 0/2<y 0 at h
      change 0<y 0
      linarith)
  · intro n y hy
    exact flatFourier_factorial_bound hs ha (by linarith : 0<x 0/2) n (hball hy).le

lemma torusRealContinuation_analytic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) : AnalyticOnNhd ℝ (torusRealContinuation s f) {x | 0<x 0} := by
  have hre (h) : |(mFourierCoeff f h).re|≤‖f‖ :=
    (Complex.abs_re_le_norm _).trans (torusFourierCoeff_bound f h)
  have him (h) : |(mFourierCoeff f h).im|≤‖f‖ :=
    (Complex.abs_im_le_norm _).trans (torusFourierCoeff_bound f h)
  intro x hx
  apply ((flatFourier_analytic hs hre x hx).add (flatFourier_analytic hs him x hx)).congr
  filter_upwards [(axial_halfspace_open 0).mem_nhds hx] with y hy
  exact (torusRealContinuation_eq hs f hy).symm

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma pairCLM_surjective_of_minor (D : Coord3 →L[ℝ] (Fin 2 → ℝ)) (p q : Coord3)
    (hn : D p 0*D q 1-D p 1*D q 0≠0) : Function.Surjective D := by
  intro y
  refine ⟨((y 0*D q 1-y 1*D q 0)/(D p 0*D q 1-D p 1*D q 0)) • p+
    ((D p 0*y 1-D p 1*y 0)/(D p 0*D q 1-D p 1*D q 0)) • q,?_⟩
  ext j
  fin_cases j <;> simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  · change ((y 0*D q 1-y 1*D q 0)/(D p 0*D q 1-D p 1*D q 0))*D p 0+
      ((D p 0*y 1-D p 1*y 0)/(D p 0*D q 1-D p 1*D q 0))*D q 0=y 0
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,←add_div,div_eq_iff hn]
    ring
  · change ((y 0*D q 1-y 1*D q 0)/(D p 0*D q 1-D p 1*D q 0))*D p 1+
      ((D p 0*y 1-D p 1*y 0)/(D p 0*D q 1-D p 1*D q 0))*D q 1=y 1
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,←add_div,div_eq_iff hn]
    ring

lemma potential_component_fderivAt {u : Coord3 → Fin 2 → ℝ} {x : Coord3}
    (hu : DifferentiableAt ℝ u x) (j : Fin 2) (v : Coord3) :
    fderiv ℝ (fun y => u y j) x v=fderiv ℝ u x v j := by
  rw [(hasFDerivAt_pi'.mp hu.hasFDerivAt j).fderiv]
  rfl

theorem analyticPair_regular_of_patch {u : Coord3 → Fin 2 → ℝ}
    {A : Coord3 → Symmetric3} {U O : Set Coord3}
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hu : ∀ j,AnalyticOnNhd ℝ (fun x => u x j) U)
    (hA : ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun x => (A x).val) U)
    (hO : IsOpen O) (hOU : O⊆U) (hne : O.Nonempty)
    (hr : TwoFieldRankRegular u O) :
    ∀ᵐ x : Coord3,x∈U → x∈regularRegion u A U := by
  have hus : ContDiffOn ℝ (↑(⊤:ℕ∞)) u U :=
    (AnalyticOnNhd.pi hu).contDiffOn_of_completeSpace
  have hud (x) (hx : x∈U) :=
    (hus.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)
  obtain ⟨a,ha⟩ := hne
  rcases hr with hr|hr|⟨κ,hκ⟩
  · have hs := gradientColumns_surjective _ (hr a ha)
    obtain ⟨p,hp⟩ := hs ![1,0]
    obtain ⟨q,hq⟩ := hs ![0,1]
    let M : Coord3 → ℝ := fun x =>
      fderiv ℝ (fun y => u y 0) x p*fderiv ℝ (fun y => u y 1) x q-
      fderiv ℝ (fun y => u y 0) x q*fderiv ℝ (fun y => u y 1) x p
    have hM : AnalyticOnNhd ℝ M U := analytic_gradient_minor (hu 0) (hu 1) p q
    have hMa : M a≠0 := by
      dsimp only [M]
      simp only [potential_component_fderivAt (hud a (hOU ha)),hp,hq]
      norm_num
    have hz := analyticNull_fin 3 U M hU hc hM ⟨a,hOU ha,hMa⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hn : M x≠0 := by simpa [hxu] using hx
    have hh := Filter.inter_mem (hU.mem_nhds hxu) ((hM x hxu).continuousAt.eventually_ne hn)
    obtain ⟨V,hVsub,hV,hxV⟩ := mem_nhds_iff.mp hh
    have hVU : V⊆U := fun y hy => (hVsub hy).1
    refine mem_regularRegion_iff.mpr ⟨V,hVU,⟨hV,hus.mono hVU,hA.mono hVU,Or.inl ?_⟩,hxV⟩
    intro y hy
    apply gradientColumns_rank
    apply pairCLM_surjective_of_minor _ p q
    have hn := (hVsub hy).2
    change M y≠0 at hn
    dsimp only [M] at hn
    simpa only [potential_component_fderivAt (hud y (hVU hy)),mul_comm] using hn
  · obtain ⟨v,l,κ,hv,hl,hd,he⟩ := hr
    obtain ⟨j,hj⟩ := hl
    let l' : Fin 2 → ℝ := fun k => l k/l j
    let κ' : Fin 2 → ℝ := fun k => κ k-(l k/l j)*κ j
    have heg (k : Fin 2) : EqOn (fun x => u x k)
        (fun x => l' k*u x j+κ' k) U := by
      apply (hu k).eqOn_of_preconnected_of_eventuallyEq
        ((analyticOnNhd_const.mul (hu j)).add analyticOnNhd_const) hc (hOU ha)
      filter_upwards [hO.mem_nhds ha] with x hx
      change u x k = l' k*u x j+κ' k
      dsimp only [l',κ']
      rw [he x hx k,he x hx j]
      field_simp [hj]
      ring
    have hev : (fun x => u x j)=ᶠ[𝓝 a] (fun x => l j*v x+κ j) :=
      Filter.Eventually.mono (hO.mem_nhds ha) (fun x hx => he x hx j)
    have hvd := (hv.differentiableOn (by simp) a ha).differentiableAt (hO.mem_nhds ha)
    have hf : fderiv ℝ (fun x => u x j) a=l j • fderiv ℝ v a := by
      rw [hev.fderiv_eq,((hvd.hasFDerivAt.const_mul (l j)).add_const (κ j)).fderiv]
    have hfn : fderiv ℝ (fun x => u x j) a≠0 := by
      rw [hf]
      exact smul_ne_zero hj (hd a ha)
    obtain ⟨w,hw⟩ : ∃ w : Coord3,fderiv ℝ (fun x => u x j) a w≠0 := by
      by_contra! h
      exact hfn (ContinuousLinearMap.ext h)
    have hD := analytic_directional_fderiv (hu j) w
    have hz := analyticNull_fin 3 U (fun x => fderiv ℝ (fun y => u y j) x w)
      hU hc hD ⟨a,hOU ha,hw⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hn : fderiv ℝ (fun y => u y j) x w≠0 := by simpa [hxu] using hx
    have hh := Filter.inter_mem (hU.mem_nhds hxu) ((hD x hxu).continuousAt.eventually_ne hn)
    obtain ⟨V,hVsub,hV,hxV⟩ := mem_nhds_iff.mp hh
    have hVU : V⊆U := fun y hy => (hVsub hy).1
    refine mem_regularRegion_iff.mpr ⟨V,hVU,⟨hV,hus.mono hVU,hA.mono hVU,
      Or.inr (Or.inl ⟨fun y => u y j,l',κ',(hu j).contDiffOn_of_completeSpace.mono hVU,
        ⟨j,?_⟩,?_,fun y hy k => heg k (hVU hy)⟩)⟩,hxV⟩
    · simp [l',hj]
    · intro y hy hyz
      exact (hVsub hy).2 (by rw [hyz]; rfl)
  · have heg (k : Fin 2) : EqOn (fun x => u x k) (fun _ => κ k) U := by
      apply (hu k).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hc (hOU ha)
      filter_upwards [hO.mem_nhds ha] with x hx
      exact congrFun (hκ x hx) k
    exact ae_of_all _ (fun x hx => mem_regularRegion_iff.mpr
      ⟨U,Subset.rfl,⟨hU,hus,hA,Or.inr (Or.inr ⟨κ,fun y hy => funext (fun k => heg k hy)⟩)⟩,hx⟩)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FlatSpliceRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma torusAffineField_analytic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (κ : ℝ) (f : TorusL2) :
    AnalyticOnNhd ℝ (torusAffineField s κ f) {x | 0<x 0} := by
  exact (analyticOnNhd_const.mul ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 3 => ℝ) 0).analyticOnNhd _)).add
    (torusRealContinuation_analytic hs f)

lemma branchInitialPair_regular {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (i : Fin 3) (z : TorusEndingData s (branchNormalize i f)) :
    ∀ᵐ x : Coord3,0<x 0 → x∈regularRegion
      (fun y j => torusAffineField s (centralBasisSlopes j i) (f j) y)
      (fun _ => ⟨flatBackgroundTensor s,flatBackgroundTensor_symm s⟩) {x | 0<x 0} := by
  let V := {x : Coord3 | x 0∈Ioo z.d (z.d+z.e)}
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_apply 0)
  have hne : V.Nonempty := ⟨![z.d+z.e/2,0,0],by
    change z.d<z.d+z.e/2 ∧ z.d+z.e/2<z.d+z.e
    constructor <;> linarith [z.e_pos]⟩
  obtain ⟨x,hx,hreg⟩  := Measure.exists_mem_of_measure_ne_zero_of_ae (hV.measure_ne_zero volume hne)
    (ae_restrict_of_ae (branchFinitePair i z).regular)
  obtain ⟨O,hOsub,hO,hxO⟩ := mem_regularRegion_iff.mp (hreg hx.1)
  have hvp : ∀ y∈O∩V,0<y 0 := fun y hy => z.d_pos.trans hy.2.1
  apply analyticPair_regular_of_patch (axial_halfspace_open 0) (axial_halfspace_connected 0)
    (fun j => torusAffineField_analytic hs _ _) contDiffOn_const (hO.1.inter hV) hvp ⟨x,hxO,hx⟩
  exact ((hO.2.2.2.mono inter_subset_left).congr (hO.1.inter hV)
    (fun y hy => (branchFinitePair_initial hs i z y hy.2).symm))

theorem branchSpliced_regular {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (i : Fin 3) (z : TorusEndingData s (branchNormalize i f)) :
    ∀ᵐ x : Coord3,0<x 0 → x∈regularRegion
      (fun y j => branchSplicedField i z j y)
      (fun y => ⟨branchSplicedTensor i z y,branchSplicedTensor_symm i z y⟩) {x | 0<x 0} := by
  filter_upwards [branchInitialPair_regular hs i z,(branchFinitePair i z).regular,
    ae_coord3_ne 0 (z.d+5*z.e/8)] with x hi hf hn hx
  by_cases ht : x 0<z.d+5*z.e/8
  · apply mem_regularRegion_congr_nhds (hi hx) ?_ ?_ (axial_halfspace_open 0) hx
    · filter_upwards [Filter.eventually_all.mpr (fun j =>
        branchSplicedField_initial i z hs j (by linarith [z.e_pos] : x 0<z.d+3*z.e/4))] with y hy
      exact funext hy
    · filter_upwards [(isOpen_lt (continuous_apply (0:Fin 3)) continuous_const).mem_nhds ht] with y hy
      exact Subtype.ext (ite_eq_left hy)
  · have ht' : z.d+5*z.e/8<x 0 := lt_of_le_of_ne (not_lt.mp ht) hn.symm
    apply mem_regularRegion_congr_nhds (hf (by linarith [z.e_pos])) ?_ ?_
      (axial_halfspace_open 0) hx
    · filter_upwards [Filter.eventually_all.mpr (fun j =>
        branchSplicedField_final i z j (by linarith [z.e_pos] : z.d+z.e/2<x 0))] with y hy
      exact funext hy
    · filter_upwards [(axial_halfspace_open (z.d+5*z.e/8)).mem_nhds ht'] with y hy
      exact Subtype.ext (ite_eq_right (not_lt.mpr hy.le))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalRankTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma branchCollar_regular_ae {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (i : Fin 3) (z : TorusEndingData s (branchNormalize i f))
    {a b l r : ℝ} (ha : a≠0) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Ioo l r,0<a*(t-b)) :
    ∀ᵐ y∂volume.restrict (sourceClosedCollarBand l r),
      y∈regularRegion (variableCollarField (fun x j => branchSplicedField i z j x) a b)
        (fun x => ⟨variableCollarTensor (branchSplicedTensor i z) a b x,
          variableCollarTensor_symm (branchSplicedTensor_symm i z) a b x⟩) univ := by
  apply sourceClosedCollarBand_ae_faces hl hr
  intro m n
  have hh := sourceFaceAngles_ae (flatEndCoordinates_ae ha b (branchSpliced_regular hs i z)) m n
  filter_upwards [ae_restrict_of_ae hh,sourceExtendedBox_open_ae hl hr,
    sourceExtendedBox_axial_strict_ae l r] with x hx hxo hxt
  have hh := variableCollar_regular_at (branchSplicedTensor_symm i z) ha b m n hxo
    (hx (hT _ hxt))
  exact mem_regularRegion_congr_nhds hh Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl
    isOpen_univ (mem_univ _)

lemma sourceChildInverse_fderiv_surjective (k : Fin 2) (y : Coord3) :
    Function.Surjective (fderiv ℝ (sourceChildHomeomorph (actualChildSign k)).symm y) := by
  rw [(sourceChildInverse_hasFDeriv _ y).fderiv]
  intro v
  refine ⟨sourceChildDerivative v,?_⟩
  rw [sourceChildInverseDerivative_apply,sourceChildDerivative_apply]
  ext i
  fin_cases i <;> simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;> norm_num [sourceScale]

lemma sourceChildTensorPush_contDiffOn (k : Fin 2) {K : Coord3 → Mat3} {U : Set Coord3}
    (hK : ContDiffOn ℝ (↑(⊤:ℕ∞)) K U) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (sourceChildTensorPush k K)
      ((sourceChildHomeomorph (actualChildSign k)).symm ⁻¹' U) := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact contDiffOn_const.mul (((contDiffOn_pi.mp
    (contDiffOn_pi.mp hK (childAxis i)) (childAxis j))).comp
      (sourceChildInverse_contDiff _).contDiffOn (fun _ hx => hx))

lemma sourceChild_regular_at (k : Fin 2) {u : Coord3 → Fin 2 → ℝ} {K : Coord3 → Mat3}
    (hK : ∀ x,(K x).IsSymm) {U : Set Coord3} {y : Coord3}
    (hy : (sourceChildHomeomorph (actualChildSign k)).symm y∈
      regularRegion u (fun x => ⟨K x,hK x⟩) U) :
    y∈regularRegion (fun x => u ((sourceChildHomeomorph (actualChildSign k)).symm x))
      (fun x => ⟨sourceChildTensorPush k K x,sourceChildTensorPush_symmetric k K hK x⟩)
      ((sourceChildHomeomorph (actualChildSign k)).symm ⁻¹' U) := by
  obtain ⟨O,hOU,hO,hyO⟩ := mem_regularRegion_iff.mp hy
  refine mem_regularRegion_iff.mpr ⟨(sourceChildHomeomorph (actualChildSign k)).symm ⁻¹' O,
    preimage_mono hOU,?_,hyO⟩
  exact RegularPatch.comp hO (hO.1.preimage (sourceChildHomeomorph _).symm.continuous)
    (sourceChildInverse_contDiff _).contDiffOn (fun _ hx => hx)
    (fun x _ => sourceChildInverse_fderiv_surjective k x)
    (sourceChildTensorPush_contDiffOn k hO.2.2.1)

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralCorrectedRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma parent_open_time {t : ℝ} (ht : t∈Ioo 0 centralThickness) :
    0<z.compression 0*(t-centralThickness) := mul_pos_of_neg_of_neg z.compression_parent (sub_neg.mpr ht.2)
lemma child_open_time (k : Fin 2) {t : ℝ} (ht : t∈Ioo (-centralThickness) 0) :
    0<z.compression k.succ*(t-(-centralThickness)) := mul_pos (z.compression_child k) (sub_pos.mpr ht.1)

lemma endRepresentative_regular_oai
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hS : ∀ i y,(variableEndTensor (fun i => branchSplicedTensor i (z.ending i)) z.compression i y).IsSymm)
    (i : Fin 3) : ∀ᵐ y : Coord3,y∈physicalEndRegion i →
      y∈regularRegion (z.endRepresentative i)
        (fun y => ⟨variableEndTensor (fun i => branchSplicedTensor i (z.ending i)) z.compression i y,hS i y⟩) univ := by
  refine Fin.cases ?_ (fun k => ?_) i
  · exact (ae_restrict_iff' (physicalEndRegion_compact 0).measurableSet).mp
      (branchCollar_regular_ae hs 0 (z.ending 0) (z.compression_ne 0)
        (by norm_num : -(1:ℝ)/100≤0) (by norm_num [centralThickness] : centralThickness≤(1:ℝ)/100)
        (fun t => z.parent_open_time))
  · have hh := branchCollar_regular_ae hs k.succ (z.ending k.succ) (z.compression_ne k.succ)
      (by norm_num [centralThickness] : -(1:ℝ)/100≤-centralThickness) (by norm_num : (0:ℝ)≤1/100)
      (fun t => z.child_open_time k)
    have hh' := (sourceChildInverse_quasi (actualChildSign k)).ae
      ((ae_restrict_iff' childEndBand_measurable).mp hh)
    filter_upwards [hh'] with y hy hyE
    have hr := sourceChild_regular_at k
      (variableCollarTensor_symm (branchSplicedTensor_symm k.succ (z.ending k.succ))
        (z.compression k.succ) (-centralThickness)) (hy hyE)
    simpa only [preimage_univ, endRepresentative, variableEndTensor, Fin.cases_succ] using hr

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.PhysicalFiniteEndingData.endRepresentative_regular_oai := @OAI.ScalarConductivity.PhysicalFiniteEndingData.endRepresentative_regular_oai
