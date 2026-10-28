-- Prove2me | solution 1 for MatrixTail.Master.theorem3_6
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-25T08:37:23.902165+00:00
-- url     : https://prove2.me/submissions/c9bd99e4-a2b3-43f0-9e36-04d9865d7159

import Mathlib
import Definitions.Def_MatrixTail_Master_Model


section
open Set Filter Topology
namespace MatrixTailProof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma concave_affine_majorant {s : Set E} {f : E → ℝ} (hs : IsOpen s)
    (hf : ConcaveOn ℝ s f) (hc : ContinuousOn f s) {m : E} (hm : m ∈ s) :
    ∃ L : E →L[ℝ] ℝ, ∀ x ∈ s, f x ≤ f m + L (x-m) := by
  let G : Set (E × ℝ) := {p | p.1 ∈ s ∧ p.2 < f p.1}
  have hGo : IsOpen G := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hfc : ContinuousAt f p.1 := hc.continuousAt (hs.mem_nhds hp.1)
    have hv : ∀ᶠ q : E × ℝ in 𝓝 p, q.2 < f q.1 :=
      continuous_snd.continuousAt.eventually_lt (hfc.comp continuous_fst.continuousAt) hp.2
    filter_upwards [continuous_fst.continuousAt.eventually (hs.mem_nhds hp.1), hv] with q hq hq'
    exact ⟨hq,hq'⟩
  obtain ⟨F,hF⟩ := geometric_hahn_banach_open_point hf.convex_strict_hypograph hGo
    (show (m,f m) ∉ G by simp [G])
  let L₀ : E →L[ℝ] ℝ := F.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let c : ℝ := F (0,1)
  have splitF (x : E) (y : ℝ) : F (x,y) = L₀ x + c*y := by
    have h : (x,y) = (x,0) + y • (0,1) := by ext <;> simp
    rw [h,map_add,map_smul]
    simp [L₀,c,mul_comm]
  have hcpos : 0 < c := by
    have h := hF (m,f m-1) (show (m,f m-1) ∈ G from ⟨hm,by linarith⟩)
    rw [splitF,splitF] at h
    linarith
  have hbound (x : E) (hx : x ∈ s) : L₀ x + c*f x ≤ L₀ m + c*f m := by
    by_contra h
    have hd : 0 < L₀ x + c*f x - (L₀ m + c*f m) := by linarith
    let e := (L₀ x+c*f x-(L₀ m+c*f m))/(2*c)
    have he : 0 < e := div_pos hd (by positivity)
    have hsep := hF (x,f x-e) (show (x,f x-e) ∈ G from ⟨hx,by linarith⟩)
    rw [splitF,splitF] at hsep
    have heq : e*(2*c)=L₀ x+c*f x-(L₀ m+c*f m) := div_mul_cancel₀ _ (by positivity)
    nlinarith
  refine ⟨(-c⁻¹) • L₀,?_⟩
  intro x hx
  have hb := hbound x hx
  simp only [smul_apply, map_sub, smul_eq_mul]
  have hb' := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hcpos.le)
  simp only [mul_add, ← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul] at hb'
  nlinarith
end MatrixTailProof
end

section
open MeasureTheory Set Filter Topology
namespace MatrixTailProof
variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
lemma open_concave_jensen {s : Set E} {f : E → ℝ} (hs : IsOpen s)
    (hf : ConcaveOn ℝ s f) (hc : ContinuousOn f s) (hn : ∀ x ∈ s, 0 ≤ f x)
    {A : Ω → E} (hA : Integrable A P) (hAs : ∀ ω, A ω ∈ s)
    (hm : (∫ ω, A ω ∂P) ∈ s) (hfm : AEStronglyMeasurable (fun ω => f (A ω)) P) :
    Integrable (fun ω => f (A ω)) P ∧
      (∫ ω, f (A ω) ∂P) ≤ f (∫ ω, A ω ∂P) := by
  let m := ∫ ω, A ω ∂P
  obtain ⟨L,hL⟩ := concave_affine_majorant hs hf hc hm
  have hb : Integrable (fun ω => f m + L (A ω-m)) P :=
    (integrable_const _).add (L.integrable_comp (hA.sub (integrable_const _)))
  have hfi : Integrable (fun ω => f (A ω)) P := hb.mono' hfm (by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hn _ (hAs ω))]
    exact hL _ (hAs ω))
  refine ⟨hfi,?_⟩
  calc
    (∫ ω, f (A ω) ∂P) ≤ ∫ ω, f m + L (A ω-m) ∂P := integral_mono hfi hb (fun ω => hL _ (hAs ω))
    _ = f m := by
      have hsub : Integrable (fun ω => A ω-m) P := hA.sub (integrable_const m)
      have hlin : Integrable (fun ω => L (A ω-m)) P := L.integrable_comp hsub
      have hsum := integral_add (integrable_const (f m)) hlin
      change (∫ ω, f m + L (A ω-m) ∂P) = (∫ ω, f m ∂P) + (∫ ω, L (A ω-m) ∂P) at hsum
      rw [hsum, L.integral_comp_comm hsub]
      have hi := integral_sub hA (integrable_const m)
      change (∫ ω, A ω-m ∂P) = (∫ ω, A ω ∂P) - (∫ ω, m ∂P) at hi
      rw [hi]
      simp [m]
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master
namespace MatrixTailProof
variable {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
lemma mexp_eq_exp (hA : A.IsHermitian) : mexp A = NormedSpace.exp A :=
  CFC.real_exp_eq_normedSpace_exp hA
lemma mexp_isHermitian (A : Matrix (Fin d) (Fin d) ℂ) : (mexp A).IsHermitian :=
  cfc_predicate _ A
lemma mlog_isHermitian (A : Matrix (Fin d) (Fin d) ℂ) : (mlog A).IsHermitian :=
  cfc_predicate _ A
lemma mlog_mexp (hA : A.IsHermitian) : mlog (mexp A) = A := by
  change CFC.log (mexp A) = A
  rw [mexp_eq_exp hA, CFC.log_exp A hA]
lemma mexp_posDef (hA : A.IsHermitian) : (mexp A).PosDef := by
  rw [mexp_eq_exp hA]
  have hp : (NormedSpace.exp A).PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp
      (IsSelfAdjoint.exp_nonneg (show IsSelfAdjoint A from hA))
  exact hp.posDef_iff_isUnit.mpr (Matrix.isUnit_exp A)
lemma mexp_mlog (hA : A.PosDef) : mexp (mlog A) = A := by
  rw [mexp_eq_exp (mlog_isHermitian A)]
  exact CFC.exp_log A hA.isStrictlyPositive
lemma trace_cfc_sum (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (Matrix.trace (cfc f A)).re = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle]
  simp
lemma trExp_nonneg (hA : A.IsHermitian) : 0 ≤ trExp A := by
  unfold trExp mexp
  rw [trace_cfc_sum hA]
  exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
lemma posDef_mix (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1-t) • A + t • B).PosDef := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simpa using hA
  exact Matrix.PosDef.posSemidef_add (hA.posSemidef.smul (sub_nonneg.mpr ht1)) (hB.smul ht)
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master
namespace MatrixTailProof
noncomputable def entryCLM {d : ℕ} (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A => A i j
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
lemma matrix_single_sum {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    A = ∑ i, ∑ j, A i j • Matrix.single i j 1 := by
  ext a b
  simp [Matrix.sum_apply, Matrix.single, Matrix.of_apply, ite_and]
lemma matrix_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {X : Ω → Matrix (Fin d) (Fin d) ℂ} (hX : MatIntegrable P X) :
    Integrable X P := by
  have he : X = fun ω => ∑ i, ∑ j, X ω i j • Matrix.single i j 1 := by
    funext ω
    exact matrix_single_sum (X ω)
  rw [he]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hX i j).smul_const _))
lemma mean_eq_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {X : Ω → Matrix (Fin d) (Fin d) ℂ} (hX : MatIntegrable P X) :
    mean P X = ∫ ω, X ω ∂P := by
  ext i j
  exact (entryCLM i j).integral_comp_comm (matrix_integrable hX)
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master
namespace MatrixTailProof
abbrev Herm (d : ℕ) := selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
def pdCone (d : ℕ) : Set (Herm d) := {A | (A : Matrix (Fin d) (Fin d) ℂ).PosDef}
lemma pdCone_open (d : ℕ) : IsOpen (pdCone d) := by
  have h := (upperHemicontinuous_iff_isOpen_preimage_Iic.mp
    (upperHemicontinuous_spectrum ℝ (Matrix (Fin d) (Fin d) ℂ))) (Ioi 0) isOpen_Ioi
  have heq : pdCone d = (fun A : Herm d => (A : Matrix (Fin d) (Fin d) ℂ)) ⁻¹'
      {A | spectrum ℝ A ⊆ Ioi 0} := by
    ext A
    simp only [pdCone, mem_ofPred_eq, mem_preimage, Set.subset_def, mem_Ioi]
    rw [← Matrix.isStrictlyPositive_iff_posDef,
      CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos]
    exact and_iff_right A.property
  rw [heq]
  exact h.preimage continuous_subtype_val
lemma pdCone_convex (d : ℕ) : Convex ℝ (pdCone d) := by
  intro A hA B hB a b ha hb hab
  change (a • (A : Matrix (Fin d) (Fin d) ℂ) + b • (B : Matrix (Fin d) (Fin d) ℂ)).PosDef
  have he : a = 1-b := by linarith
  rw [he]
  exact posDef_mix hA hB hb (by linarith)
lemma trExp_continuous (d : ℕ) : Continuous (fun A : Herm d => trExp (A : Matrix (Fin d) (Fin d) ℂ)) := by
  have he : (fun A : Herm d => trExp (A : Matrix (Fin d) (Fin d) ℂ)) = fun A : Herm d => (Matrix.trace (NormedSpace.exp (A : Matrix (Fin d) (Fin d) ℂ))).re := by
    funext A
    exact congrArg (fun M => (Matrix.trace M).re) (mexp_eq_exp A.property)
  rw [he]
  have hex : Continuous (NormedSpace.exp : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) :=
    continuous_iff_continuousAt.mpr (fun A => (NormedSpace.exp_analytic (𝕂 := ℂ) A).continuousAt)
  fun_prop
lemma log_continuousOn (d : ℕ) : ContinuousOn (fun A : Herm d => mlog (A : Matrix (Fin d) (Fin d) ℂ)) (pdCone d) := by
  exact CFC.continuousOn_log.comp continuous_subtype_val.continuousOn (fun A hA => ⟨A.property,hA.isUnit⟩)
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master
namespace MatrixTailProof
instance hermComplete (d : ℕ) : CompleteSpace (Herm d) :=
  (show IsClosed {A : Matrix (Fin d) (Fin d) ℂ | star A = A} from isClosed_eq continuous_star continuous_id).completeSpace_coe
noncomputable def hermPart {d : ℕ} : Matrix (Fin d) (Fin d) ℂ →L[ℝ] Herm d :=
  (selfAdjointPart ℝ).toContinuousLinearMap
lemma hermPart_coe {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    (hermPart A : Matrix (Fin d) (Fin d) ℂ) = A :=
  IsSelfAdjoint.coe_selfAdjointPart_apply ℝ hA
lemma herm_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {A : Ω → Matrix (Fin d) (Fin d) ℂ} (hA : MatIntegrable P A) :
    Integrable (fun ω => hermPart (A ω)) P :=
  hermPart.integrable_comp (matrix_integrable hA)
lemma herm_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {A : Ω → Matrix (Fin d) (Fin d) ℂ} (hA : MatIntegrable P A) :
    (∫ ω, hermPart (A ω) ∂P) = hermPart (mean P A) := by
  rw [mean_eq_integral hA]
  exact hermPart.integral_comp_comm (matrix_integrable hA)
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master Matrix
namespace MatrixTailProof
noncomputable def quadraticCLM {d : ℕ} (v : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ →L[ℂ] ℂ :=
  ∑ i, ∑ j, (star (v i) * v j) • entryCLM i j
lemma quadraticCLM_apply {d : ℕ} (v : Fin d → ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    quadraticCLM v A = star v ⬝ᵥ (A *ᵥ v) := by
  simp only [quadraticCLM, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, entryCLM, 
    Matrix.mulVec, dotProduct, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (star (v i) * v j) * A i j = star (v i) * (A i j * v j)
  ring
lemma mean_isHermitian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {X : Ω → Matrix (Fin d) (Fin d) ℂ} (hX : ∀ ω, (X ω).IsHermitian) :
    (mean P X).IsHermitian := by
  ext i j
  change starRingEnd ℂ (∫ ω, X ω j i ∂P) = ∫ ω, X ω i j ∂P
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with ω
  exact congrFun (congrFun (hX ω) i) j
lemma mean_posDef {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {X : Ω → Matrix (Fin d) (Fin d) ℂ}
    (hX : MatIntegrable P X) (hp : ∀ ω, (X ω).PosDef) : (mean P X).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (mean_isHermitian (fun ω => (hp ω).isHermitian))
  intro v hv
  have hi := (quadraticCLM v).integrable_comp (matrix_integrable hX)
  have he : star v ⬝ᵥ (mean P X *ᵥ v) = ∫ ω, quadraticCLM v (X ω) ∂P := by
    rw [← quadraticCLM_apply, mean_eq_integral hX, ← (quadraticCLM v).integral_comp_comm (matrix_integrable hX)]
  rw [he, Complex.pos_iff]
  constructor
  · change 0 < RCLike.re (∫ ω, quadraticCLM v (X ω) ∂P)
    rw [← integral_re hi]
    apply (integral_pos_iff_support_of_nonneg (fun ω => by
      rw [quadraticCLM_apply]
      exact (hp ω).re_dotProduct_pos hv |>.le) hi.re).mpr
    have hs : Function.support (fun ω => RCLike.re (quadraticCLM v (X ω))) = Set.univ := by
      ext ω
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      rw [quadraticCLM_apply]
      exact ne_of_gt ((hp ω).re_dotProduct_pos hv)
    rw [hs, measure_univ]
    exact zero_lt_one
  · change 0 = RCLike.im (∫ ω, quadraticCLM v (X ω) ∂P)
    rw [← integral_im hi]
    symm
    apply integral_eq_zero_of_ae
    filter_upwards [] with ω
    rw [quadraticCLM_apply]
    exact ((Complex.pos_iff.mp ((hp ω).dotProduct_mulVec_pos hv)).2).symm
end MatrixTailProof
end

section
open MeasureTheory Set Filter Topology
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master
namespace MatrixTailProof
noncomputable def liebFun {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (A : Herm d) : ℝ :=
  trExp (H + mlog (A : Matrix (Fin d) (Fin d) ℂ))
lemma liebFun_nonneg {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (A : Herm d) :
    0 ≤ liebFun H A := trExp_nonneg (hH.add (mlog_isHermitian _))
lemma liebFun_continuousOn {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) :
    ContinuousOn (liebFun H) (pdCone d) := by
  have he : liebFun H = fun A : Herm d => (Matrix.trace
      (NormedSpace.exp (H + mlog (A : Matrix (Fin d) (Fin d) ℂ)))).re := by
    funext A
    exact congrArg (fun M => (Matrix.trace M).re) (mexp_eq_exp (hH.add (mlog_isHermitian _)))
  rw [he]
  have hex : Continuous (NormedSpace.exp : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) :=
    continuous_iff_continuousAt.mpr (fun A => (NormedSpace.exp_analytic (𝕂 := ℂ) A).continuousAt)
  have hb : ContinuousOn (fun A : Herm d => H + mlog (A : Matrix (Fin d) (Fin d) ℂ)) (pdCone d) :=
    continuousOn_const.add (log_continuousOn d)
  have hc := hex.comp_continuousOn hb
  have htr : Continuous (Matrix.trace : Matrix (Fin d) (Fin d) ℂ → ℂ) := by fun_prop
  exact Complex.continuous_re.comp_continuousOn (htr.comp_continuousOn hc)
lemma liebFun_concave {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ (A B : Matrix (Fin d) (Fin d) ℂ), A.PosDef → B.PosDef →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (1-t) * trExp (H + mlog A) + t * trExp (H + mlog B) ≤ trExp (H + mlog ((1-t) • A + t • B))) :
    ConcaveOn ℝ (pdCone d) (liebFun H) := by
  refine ⟨pdCone_convex d,?_⟩
  intro A hA B hB a b ha hb hab
  have he : a = 1-b := by linarith
  subst a
  exact h A B hA hB b hb (by linarith)
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master
namespace MatrixTailProof
lemma native_jensen_of_concave {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    {A : Ω → Matrix (Fin d) (Fin d) ℂ} (hA : MatIntegrable P A)
    (hp : ∀ ω, (A ω).PosDef)
    (hconc : ConcaveOn ℝ (pdCone d) (liebFun H)) :
    Integrable (fun ω => trExp (H + mlog (A ω))) P ∧
      (∫ ω, trExp (H + mlog (A ω)) ∂P) ≤ trExp (H + mlog (mean P A)) := by
  classical
  let : MeasurableSpace (Herm d) := borel (Herm d)
  let : BorelSpace (Herm d) := ⟨rfl⟩
  let B : Ω → Herm d := fun ω => hermPart (A ω)
  have hbi : Integrable B P := herm_integrable hA
  have hb : ∀ ω, B ω ∈ pdCone d := by
    intro ω
    change (hermPart (A ω) : Matrix (Fin d) (Fin d) ℂ).PosDef
    rw [hermPart_coe (hp ω).isHermitian]
    exact hp ω
  have hm : (∫ ω, B ω ∂P) ∈ pdCone d := by
    rw [show (∫ ω, B ω ∂P) = hermPart (mean P A) from herm_integral hA]
    change (hermPart (mean P A) : Matrix (Fin d) (Fin d) ℂ).PosDef
    rw [hermPart_coe (mean_posDef hA hp).isHermitian]
    exact mean_posDef hA hp
  have hc := liebFun_continuousOn hH
  have hpiece : Measurable ((pdCone d).piecewise (liebFun H) (fun _ => 0)) :=
    hc.measurable_piecewise continuousOn_const (pdCone_open d).measurableSet
  have hfm : AEStronglyMeasurable (fun ω => liebFun H (B ω)) P := by
    have h := hpiece.comp_aemeasurable hbi.aestronglyMeasurable.aemeasurable
    have he : (fun ω => (pdCone d).piecewise (liebFun H) (fun _ => 0) (B ω)) =
        (fun ω => liebFun H (B ω)) := by
      funext ω
      exact Set.piecewise_eq_of_mem _ _ _ (hb ω)
    change AEMeasurable (fun ω => (pdCone d).piecewise (liebFun H) (fun _ => 0) (B ω)) P at h
    rw [he] at h
    exact h.aestronglyMeasurable
  have hj := open_concave_jensen (pdCone_open d) hconc hc
    (fun x _ => liebFun_nonneg hH x) hbi hb hm hfm
  have he : (fun ω => liebFun H (B ω)) = (fun ω => trExp (H + mlog (A ω))) := by
    funext ω
    unfold liebFun B
    rw [hermPart_coe (hp ω).isHermitian]
  rw [he] at hj
  refine ⟨hj.1,?_⟩
  convert hj.2 using 1
  rw [show (∫ ω, B ω ∂P) = hermPart (mean P A) from herm_integral hA]
  unfold liebFun
  rw [hermPart_coe (mean_posDef hA hp).isHermitian]
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master
namespace MatrixTailProof
lemma exponential_jensen_of_concave {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    {Z : Ω → Matrix (Fin d) (Fin d) ℂ} (hZ : ∀ ω, (Z ω).IsHermitian)
    (hi : MatIntegrable P (fun ω => mexp (Z ω)))
    (hconc : ConcaveOn ℝ (pdCone d) (liebFun H)) :
    Integrable (fun ω => trExp (H + Z ω)) P ∧
      (∫ ω, trExp (H + Z ω) ∂P) ≤ trExp (H + mlog (mean P (fun ω => mexp (Z ω)))) := by
  have h := native_jensen_of_concave hH hi (fun ω => mexp_posDef (hZ ω)) hconc
  have he : (fun ω => trExp (H + mlog (mexp (Z ω)))) = (fun ω => trExp (H + Z ω)) := by
    funext ω
    rw [mlog_mexp (hZ ω)]
  rwa [he] at h
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master
namespace MatrixTailProof
instance nativeMatrixBorel (d : ℕ) : BorelSpace (Matrix (Fin d) (Fin d) ℂ) := by
  change BorelSpace (Fin d → Fin d → ℂ)
  infer_instance
noncomputable def traceExpAll {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (Matrix.trace (NormedSpace.exp A)).re
lemma traceExpAll_eq {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    traceExpAll A = trExp A := by
  unfold traceExpAll trExp
  rw [mexp_eq_exp hA]
lemma traceExpAll_continuous (d : ℕ) : Continuous (traceExpAll : Matrix (Fin d) (Fin d) ℂ → ℝ) := by
  have hex : Continuous (NormedSpace.exp : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) :=
    continuous_iff_continuousAt.mpr (fun A => (NormedSpace.exp_analytic (𝕂 := ℂ) A).continuousAt)
  unfold traceExpAll
  fun_prop
lemma trExp_measurable_comp {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : Ω → Matrix (Fin d) (Fin d) ℂ} (hX : Measurable X) (hh : ∀ ω, (X ω).IsHermitian) :
    Measurable (fun ω => trExp (X ω)) := by
  have he : (fun ω => trExp (X ω)) = traceExpAll ∘ X := by
    funext ω
    exact (traceExpAll_eq (hh ω)).symm
  rw [he]
  exact (traceExpAll_continuous d).measurable.comp hX
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory Set
namespace MatrixTailProof
lemma positive_fubini_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → ℝ} {g : α → ℝ} (hf : AEStronglyMeasurable f (μ.prod ν))
    (hn : ∀ x, 0 ≤ f x) (hfi : ∀ x, Integrable (fun y => f (x,y)) ν)
    (hg : Integrable g μ) (hb : ∀ x, (∫ y, f (x,y) ∂ν) ≤ g x) :
    Integrable f (μ.prod ν) ∧ (∫ z, f z ∂(μ.prod ν)) ≤ ∫ x, g x ∂μ := by
  have hi : AEStronglyMeasurable (fun x => ∫ y, f (x,y) ∂ν) μ := hf.integral_prod_right'
  have hii : Integrable (fun x => ∫ y, f (x,y) ∂ν) μ := hg.mono' hi (by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun y => hn (x,y)))]
    exact hb x)
  have hnorm : (fun x => ∫ y, ‖f (x,y)‖ ∂ν) = (fun x => ∫ y, f (x,y) ∂ν) := by
    funext x
    apply integral_congr_ae
    filter_upwards [] with y
    exact Real.norm_of_nonneg (hn (x,y))
  have hip : Integrable f (μ.prod ν) := (integrable_prod_iff hf).mpr
    ⟨Filter.Eventually.of_forall hfi, hnorm ▸ hii⟩
  refine ⟨hip,?_⟩
  rw [integral_prod _ hip]
  exact integral_mono hii hg hb
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory
namespace MatrixTailProof
lemma independent_product_law {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → E} {Y : Ω → F} (hX : Measurable X) (hY : Measurable Y)
    (hI : IndepFun X Y P) :
    IdentDistrib (fun ω => (X ω,Y ω)) (fun z : Ω × Ω => (X z.1,Y z.2)) P (P.prod P) := by
  refine ⟨(hX.prodMk hY).aemeasurable, (hX.prodMap hY).aemeasurable,?_⟩
  rw [hI.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
  exact Measure.map_prod_map P P hX hY
lemma independent_integral_transfer {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → E} {Y : Ω → F} (hX : Measurable X) (hY : Measurable Y)
    (hI : IndepFun X Y P) {f : E × F → ℝ} (hf : Measurable f)
    (hi : Integrable (fun z : Ω × Ω => f (X z.1,Y z.2)) (P.prod P)) :
    Integrable (fun ω => f (X ω,Y ω)) P ∧
      (∫ ω, f (X ω,Y ω) ∂P) = ∫ z, f (X z.1,Y z.2) ∂(P.prod P) := by
  have h := (independent_product_law hX hY hI).comp hf
  exact ⟨h.integrable_iff.mpr hi, h.integral_eq⟩
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master
namespace MatrixTailProof
lemma independent_cgf_step {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ}
    (hL : ∀ H : Matrix (Fin d) (Fin d) ℂ, H.IsHermitian → ConcaveOn ℝ (pdCone d) (liebFun H))
    {Y Z : Ω → Matrix (Fin d) (Fin d) ℂ} (hYm : Measurable Y) (hZm : Measurable Z)
    (hY : ∀ ω, (Y ω).IsHermitian) (hZ : ∀ ω, (Z ω).IsHermitian)
    (hI : IndepFun Y Z P) (hZi : MatIntegrable P (fun ω => mexp (Z ω)))
    (hg : Integrable (fun ω => trExp (Y ω + mlog (mean P (fun z => mexp (Z z))))) P) :
    Integrable (fun ω => trExp (Y ω + Z ω)) P ∧
      (∫ ω, trExp (Y ω + Z ω) ∂P) ≤
        ∫ ω, trExp (Y ω + mlog (mean P (fun z => mexp (Z z)))) ∂P := by
  let f : Ω × Ω → ℝ := fun z => trExp (Y z.1 + Z z.2)
  have hfm : Measurable f := trExp_measurable_comp
    ((hYm.comp measurable_fst).add (hZm.comp measurable_snd)) (fun z => (hY z.1).add (hZ z.2))
  have hj := fun x => exponential_jensen_of_concave (hY x) hZ hZi (hL (Y x) (hY x))
  have hp := positive_fubini_bound hfm.aestronglyMeasurable
    (fun z => trExp_nonneg ((hY z.1).add (hZ z.2))) (fun x => (hj x).1) hg (fun x => (hj x).2)
  let F : Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ → ℝ :=
    fun z => traceExpAll (z.1 + z.2)
  have hF : Measurable F := (traceExpAll_continuous d).measurable.comp (measurable_fst.add measurable_snd)
  have he : (fun z : Ω × Ω => F (Y z.1,Z z.2)) = f := by
    funext z
    exact traceExpAll_eq ((hY z.1).add (hZ z.2))
  have hi : Integrable (fun z : Ω × Ω => F (Y z.1,Z z.2)) (P.prod P) := he ▸ hp.1
  have ht := independent_integral_transfer hYm hZm hI hF hi
  have hd : (fun ω => F (Y ω,Z ω)) = (fun ω => trExp (Y ω+Z ω)) := by
    funext ω
    exact traceExpAll_eq ((hY ω).add (hZ ω))
  rw [hd, he] at ht
  exact ⟨ht.1, ht.2.trans_le hp.2⟩
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master
namespace MatrixTailProof
lemma finite_cgf {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ}
    (hL : ∀ H : Matrix (Fin d) (Fin d) ℂ, H.IsHermitian → ConcaveOn ℝ (pdCone d) (liebFun H))
    (X : ι → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hXm : ∀ i, Measurable (X i)) (hX : ∀ i ω, (X i ω).IsHermitian)
    (hI : iIndepFun X P) (hi : ∀ i, MatIntegrable P (fun ω => mexp (X i ω)))
    (s : Finset ι) (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    Integrable (fun ω => trExp (H + ∑ i ∈ s, X i ω)) P ∧
      (∫ ω, trExp (H + ∑ i ∈ s, X i ω) ∂P) ≤
        trExp (H + ∑ i ∈ s, mlog (mean P (fun ω => mexp (X i ω)))) := by
  classical
  induction s using Finset.induction_on generalizing H with
  | empty => simp only [Finset.sum_empty, add_zero]; exact ⟨integrable_const _, by simp⟩
  | @insert i s his ih =>
    let C := mlog (mean P (fun ω => mexp (X i ω)))
    have hC : C.IsHermitian := mlog_isHermitian _
    have hind := ih (H+C) (hH.add hC)
    have hsm : Measurable (fun ω => ∑ j ∈ s, X j ω) := by fun_prop
    have hsH : ∀ ω, (∑ j ∈ s, X j ω).IsHermitian := fun ω => isSelfAdjoint_sum s (fun j _ => hX j ω)
    have hIs : IndepFun (fun ω => H + ∑ j ∈ s, X j ω) (X i) P := by
      have ht := (hI.indepFun_finsetSum_of_notMem hXm his).comp (φ := fun A : Matrix (Fin d) (Fin d) ℂ => H + A)
        (measurable_const.add measurable_id) measurable_id
      simpa only [Function.comp_def, Finset.sum_apply, id_eq] using ht
    have hgi : Integrable (fun ω => trExp ((H + ∑ j ∈ s, X j ω) + C)) P := by
      simpa only [add_assoc, add_comm C, add_left_comm C] using hind.1
    have hstep := independent_cgf_step hL (measurable_const.add hsm) (hXm i)
      (fun ω => hH.add (hsH ω)) (hX i) hIs (hi i) hgi
    constructor
    · have he : (fun ω => trExp (H + ∑ j ∈ insert i s, X j ω)) =
          (fun ω => trExp ((H + ∑ j ∈ s, X j ω) + X i ω)) := by
        funext ω
        rw [Finset.sum_insert his]
        congr 1
        abel
      rw [he]
      exact hstep.1
    · calc
        (∫ ω, trExp (H + ∑ j ∈ insert i s, X j ω) ∂P) =
          ∫ ω, trExp ((H + ∑ j ∈ s, X j ω) + X i ω) ∂P := by
            congr 1; funext ω; rw [Finset.sum_insert his]; congr 1; abel
        _ ≤ ∫ ω, trExp ((H + ∑ j ∈ s, X j ω) + C) ∂P := hstep.2
        _ = ∫ ω, trExp ((H+C) + ∑ j ∈ s, X j ω) ∂P := by congr 1; funext ω; congr 1; abel
        _ ≤ trExp ((H+C) + ∑ j ∈ s, mlog (mean P (fun ω => mexp (X j ω)))) := hind.2
        _ = trExp (H + ∑ j ∈ insert i s, mlog (mean P (fun ω => mexp (X j ω)))) := by
          rw [Finset.sum_insert his]; simp only [C, add_assoc]
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master
namespace MatrixTailProof
lemma lambdaMax_mem {d : ℕ} [NeZero d] {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    lambdaMax A ∈ spectrum ℝ A := by
  unfold lambdaMax
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact (Set.range_nonempty _).csSup_mem (Set.finite_range _)
lemma exp_lambda_le_trace {d : ℕ} [NeZero d] {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (θ : ℝ) : Real.exp (θ * lambdaMax A) ≤ trExp (θ • A) := by
  have hs : θ * lambdaMax A ∈ spectrum ℝ (θ • A) := by
    rw [spectrum.smul_eq_smul θ A (by exact ⟨_, lambdaMax_mem hA⟩)]
    exact ⟨lambdaMax A, lambdaMax_mem hA, rfl⟩
  have hθ : (θ • A).IsHermitian := hA.smul (show IsSelfAdjoint θ from rfl)
  rw [hθ.spectrum_real_eq_range_eigenvalues] at hs
  obtain ⟨i,hi⟩ := hs
  unfold trExp mexp
  rw [trace_cfc_sum hθ, ← hi]
  exact Finset.single_le_sum (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
lemma matrix_laplace {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} [NeZero d] {Y : Ω → Matrix (Fin d) (Fin d) ℂ}
    (hY : ∀ ω, (Y ω).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (hi : Integrable (fun ω => trExp (θ • Y ω)) P) (t : ℝ) :
    P.real {ω | t ≤ lambdaMax (Y ω)} ≤
      Real.exp (-θ*t) * ∫ ω, trExp (θ • Y ω) ∂P := by
  have hs : {ω | t ≤ lambdaMax (Y ω)} ⊆ {ω | Real.exp (θ*t) ≤ trExp (θ • Y ω)} := by
    intro ω hω
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hθ.le)).trans (exp_lambda_le_trace (hY ω) θ)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => trExp_nonneg ((hY ω).smul (show IsSelfAdjoint θ from rfl)))) hi (Real.exp (θ*t))
  have hprob : P.real {ω | t ≤ lambdaMax (Y ω)} ≤ P.real {ω | Real.exp (θ*t) ≤ trExp (θ • Y ω)} :=
    measureReal_mono hs
  have hdiv : P.real {ω | Real.exp (θ*t) ≤ trExp (θ • Y ω)} ≤
      (∫ ω, trExp (θ • Y ω) ∂P) / Real.exp (θ*t) :=
    (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using hm)
  refine hprob.trans (hdiv.trans_eq ?_)
  rw [div_eq_mul_inv, ← Real.exp_neg]
  rw [neg_mul, mul_comm]
end MatrixTailProof
end

section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace MatrixTailProof
noncomputable def quadratic {d : ℕ} (A X : Matrix (Fin d) (Fin d) ℂ) (s : ℝ)
    (Y : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (Matrix.trace (Y.conjTranspose * A * Y)).re +
    s * (Matrix.trace (Y.conjTranspose * Y * X)).re

theorem trace_star_swap {d : ℕ} (X Y : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.trace (X.conjTranspose * Y)).re = (Matrix.trace (Y.conjTranspose * X)).re := by
  have h := congrArg Complex.re (Matrix.trace_conjTranspose (X.conjTranspose * Y))
  simpa using h.symm

theorem quadratic_nonneg {d : ℕ} {A X : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosDef) (hX : X.PosDef) {s : ℝ} (hs : 0 ≤ s)
    (Y : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ quadratic A X s Y := by
  have ha : 0 ≤ (Matrix.trace (Y.conjTranspose * A * Y)).re :=
    (RCLike.nonneg_iff.mp (hA.posSemidef.conjTranspose_mul_mul_same Y).trace_nonneg).1
  have hx : 0 ≤ (Matrix.trace (Y * X * Y.conjTranspose)).re :=
    (RCLike.nonneg_iff.mp (hX.posSemidef.mul_mul_conjTranspose_same Y).trace_nonneg).1
  rw [Matrix.trace_mul_cycle] at hx
  exact add_nonneg ha (mul_nonneg hs hx)

theorem quadratic_completion {d : ℕ} {A X R : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hX : X.IsHermitian) (s : ℝ)
    (hR : A*R+s • (R*X)=X) (Y : Matrix (Fin d) (Fin d) ℂ) :
    2*(Matrix.trace (X*Y)).re - quadratic A X s Y =
      (Matrix.trace (X*R)).re - quadratic A X s (Y-R) := by
  have hleft (Z : Matrix (Fin d) (Fin d) ℂ) :
      (Matrix.trace (Z.conjTranspose*A*R)).re +
        s*(Matrix.trace (Z.conjTranspose*R*X)).re = (Matrix.trace (X*Z)).re := by
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ =>
      (Matrix.trace (Z.conjTranspose*M)).re) hR
    have hz := trace_star_swap Z X
    simp only [hX.eq] at hz
    simpa [mul_add, mul_smul_comm, Matrix.trace_add, Matrix.trace_smul,
      Complex.add_re, Complex.real_smul, mul_assoc, hz] using h
  have hright (Z : Matrix (Fin d) (Fin d) ℂ) :
      (Matrix.trace (R.conjTranspose*A*Z)).re +
        s*(Matrix.trace (R.conjTranspose*Z*X)).re = (Matrix.trace (X*Z)).re := by
    have h := hleft Z
    have h1 := trace_star_swap (A*R) Z
    have h2 := trace_star_swap (R*X) Z
    simp only [Matrix.conjTranspose_mul, hA.eq, hX.eq, mul_assoc] at h1 h2
    rw [Matrix.trace_mul_comm X (R.conjTranspose * Z)] at h2
    simp only [← mul_assoc] at h1 h2
    rw [h1, h2]
    exact h
  have hr := hleft R
  have hl := hleft Y
  have hh := hright Y
  unfold quadratic
  simp only [Matrix.conjTranspose_sub, sub_mul, mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith
end MatrixTailProof
end

section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace MatrixTailProof

noncomputable def overlap {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ := (star U * V : Matrix.unitaryGroup (Fin d) ℂ)

theorem unitary_row_normSq {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Fin d) :
    ∑ j, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (A i i).re) U.2.2
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj, map_sum] using h

theorem unitary_col_normSq {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (j : Fin d) :
    ∑ i, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (A j j).re) U.2.1
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.normSq_apply, map_sum] using h

theorem trace_diag_pair {d : ℕ} (a b : Fin d → ℝ) (C : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.trace (Matrix.diagonal (fun i => (a i : ℂ)) * C *
      Matrix.diagonal (fun j => (b j : ℂ)) * C.conjTranspose)).re =
      ∑ i, ∑ j, a i * b j * Complex.normSq (C i j) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    mul_ite, mul_zero, Finset.sum_ite_eq]
  rw [Complex.re_sum]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem trace_conj_pair {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d → ℝ) :
    (Matrix.trace (((U : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun i => (a i : ℂ)) * star (U : Matrix (Fin d) (Fin d) ℂ)) *
      ((V : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun j => (b j : ℂ)) * star (V : Matrix (Fin d) (Fin d) ℂ)))).re =
      ∑ i, ∑ j, a i * b j * Complex.normSq (overlap U V i j) := by
  have he : ((U : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun i => (a i : ℂ)) * star (U : Matrix (Fin d) (Fin d) ℂ)) *
      ((V : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun j => (b j : ℂ)) * star (V : Matrix (Fin d) (Fin d) ℂ)) =
      (U : Matrix (Fin d) (Fin d) ℂ) *
        (Matrix.diagonal (fun i => (a i : ℂ)) * overlap U V *
          Matrix.diagonal (fun j => (b j : ℂ)) * star (overlap U V)) * star (U : Matrix (Fin d) (Fin d) ℂ) := by
    simp [overlap, mul_assoc]
  rw [he, Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self, one_mul]
  exact trace_diag_pair a b (overlap U V)

theorem trace_cfc_pair {d : ℕ} {A X : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hX : X.IsHermitian) (f g : ℝ → ℝ) :
    (Matrix.trace (cfc f A * cfc g X)).re =
      ∑ i, ∑ j, f (hA.eigenvalues i) * g (hX.eigenvalues j) *
        Complex.normSq (overlap hA.eigenvectorUnitary hX.eigenvectorUnitary i j) := by
  rw [hA.cfc_eq, hX.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def]
  exact trace_conj_pair hA.eigenvectorUnitary hX.eigenvectorUnitary _ _

end MatrixTailProof
end

section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace MatrixTailProof
noncomputable def resolventEntries {d : ℕ} (a b : Fin d → ℝ) (s : ℝ)
    (C : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => ((b j / (a i + s*b j) : ℝ) : ℂ) * C i j

theorem resolventEntries_equation {d : ℕ} (a b : Fin d → ℝ) (s : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hs : 0 ≤ s)
    (C : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.diagonal (fun i => (a i : ℂ)) * resolventEntries a b s C +
      s • (resolventEntries a b s C * Matrix.diagonal (fun j => (b j : ℂ))) =
      C * Matrix.diagonal (fun j => (b j : ℂ)) := by
  ext i j
  have hden : a i + s*b j ≠ 0 := ne_of_gt (by have hai := ha i; have hbj := hb j; positivity)
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.smul_apply,
    Matrix.mul_diagonal, resolventEntries, Complex.real_smul]
  have hr : a i * (b j / (a i+s*b j)) + s*(b j/(a i+s*b j))*b j = b j := by
    calc
      _ = (b j / (a i+s*b j)) * (a i+s*b j) := by ring
      _ = b j := div_mul_cancel₀ _ hden
  calc
    _ = ((a i * (b j / (a i+s*b j)) + s*(b j/(a i+s*b j))*b j : ℝ) : ℂ) * C i j := by
      push_cast
      ring
    _ = _ := by rw [hr]; ring

theorem unitary_star_cancel {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (M : Matrix (Fin d) (Fin d) ℂ) :
    star (U : Matrix (Fin d) (Fin d) ℂ) * ((U : Matrix (Fin d) (Fin d) ℂ) * M) = M := by
  rw [← mul_assoc]
  simp

theorem unitary_cancel_star {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (M : Matrix (Fin d) (Fin d) ℂ) :
    (U : Matrix (Fin d) (Fin d) ℂ) * (star (U : Matrix (Fin d) (Fin d) ℂ) * M) = M := by
  rw [← mul_assoc]
  simp

noncomputable def unitaryResolvent {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d → ℝ) (s : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) * resolventEntries a b s (overlap U V) *
    star (V : Matrix (Fin d) (Fin d) ℂ)

theorem unitaryResolvent_equation {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d → ℝ) (s : ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hs : 0 ≤ s) :
    ((U : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun i => (a i : ℂ)) * star (U : Matrix (Fin d) (Fin d) ℂ)) *
      unitaryResolvent U V a b s + s • (unitaryResolvent U V a b s *
      ((V : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun j => (b j : ℂ)) * star (V : Matrix (Fin d) (Fin d) ℂ))) =
      (V : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun j => (b j : ℂ)) * star (V : Matrix (Fin d) (Fin d) ℂ) := by
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ =>
    (U : Matrix (Fin d) (Fin d) ℂ) * M * star (V : Matrix (Fin d) (Fin d) ℂ))
      (resolventEntries_equation a b s ha hb hs (overlap U V))
  simpa [unitaryResolvent, overlap, mul_assoc, mul_add, add_mul, mul_smul_comm,
    smul_mul_assoc, unitary_star_cancel, unitary_cancel_star] using h
end MatrixTailProof
end

section
open Matrix MatrixTail.Master
open scoped ComplexOrder MatrixOrder
namespace MatrixTailProof
noncomputable def entropy0 {d : ℕ} (X A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (Matrix.trace (X * (mlog X - mlog A))).re

theorem trace_cfc_mul {d : ℕ} {A X : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (Matrix.trace (cfc f A * X)).re =
      ∑ i, ∑ j, f (hA.eigenvalues i) * hX.eigenvalues j *
        Complex.normSq (overlap hA.eigenvectorUnitary hX.eigenvectorUnitary i j) := by
  have h := trace_cfc_pair hA hX f id
  have hx : cfc (id : ℝ → ℝ) X = X := by
    rw [hX.cfc_eq]
    exact hX.spectral_theorem.symm
  rw [hx] at h
  simpa only [id_eq] using h

theorem trace_self_log {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian) :
    (Matrix.trace (X * mlog X)).re = ∑ j, hX.eigenvalues j * Real.log (hX.eigenvalues j) := by
  rw [Matrix.trace_mul_comm]
  change (Matrix.trace (cfc Real.log X * X)).re = _
  rw [trace_cfc_mul hX hX]
  simp [overlap, Matrix.one_apply, mul_comm]

theorem entropy_spectral {d : ℕ} {X A : Matrix (Fin d) (Fin d) ℂ}
    (hX : X.IsHermitian) (hA : A.IsHermitian) :
    entropy0 X A = ∑ i, ∑ j,
      (hX.eigenvalues j * (Real.log (hX.eigenvalues j) - Real.log (hA.eigenvalues i))) *
        Complex.normSq (overlap hA.eigenvectorUnitary hX.eigenvectorUnitary i j) := by
  let C : Matrix.unitaryGroup (Fin d) ℂ := star hA.eigenvectorUnitary * hX.eigenvectorUnitary
  have hcol (j : Fin d) : ∑ i, Complex.normSq (overlap hA.eigenvectorUnitary hX.eigenvectorUnitary i j) = 1 :=
    unitary_col_normSq C j
  have hsum : (∑ i, ∑ j, (hX.eigenvalues j * Real.log (hX.eigenvalues j)) *
      Complex.normSq (overlap hA.eigenvectorUnitary hX.eigenvectorUnitary i j)) =
      ∑ j, hX.eigenvalues j * Real.log (hX.eigenvalues j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hcol, mul_one]
  unfold entropy0
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re, trace_self_log hX,
    Matrix.trace_mul_comm X (mlog A)]
  change _ - (Matrix.trace (cfc Real.log A * X)).re = _
  rw [trace_cfc_mul hA hX, ← hsum]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
end MatrixTailProof
end

section
open Matrix MatrixTail.Master
open scoped ComplexOrder MatrixOrder
namespace MatrixTailProof

theorem trace_resolventEntries {d : ℕ} (a b : Fin d → ℝ) (s : ℝ)
    (C : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.trace (Matrix.diagonal (fun j => (b j : ℂ)) * C.conjTranspose *
      resolventEntries a b s C)).re =
      ∑ i, ∑ j, (b j ^ 2 / (a i+s*b j)) * Complex.normSq (C i j) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply]
  simp only [ite_mul, zero_mul, resolventEntries]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  simp only [zero_mul, sub_zero, add_zero]
  ring

theorem trace_unitaryResolvent {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d → ℝ) (s : ℝ) :
    (Matrix.trace (((V : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun j => (b j : ℂ)) *
      star (V : Matrix (Fin d) (Fin d) ℂ)) * unitaryResolvent U V a b s)).re =
      ∑ i, ∑ j, (b j ^ 2 / (a i+s*b j)) * Complex.normSq (overlap U V i j) := by
  have he : ((V : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun j => (b j : ℂ)) *
      star (V : Matrix (Fin d) (Fin d) ℂ)) * unitaryResolvent U V a b s =
      (V : Matrix (Fin d) (Fin d) ℂ) *
        (Matrix.diagonal (fun j => (b j : ℂ)) * star (overlap U V) *
          resolventEntries a b s (overlap U V)) * star (V : Matrix (Fin d) (Fin d) ℂ) := by
    simp [unitaryResolvent, overlap, mul_assoc]
  rw [he, Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self, one_mul]
  exact trace_resolventEntries a b s (overlap U V)

theorem resolvent_certificate {d : ℕ} {A X : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosDef) (hX : X.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    ∃ R : Matrix (Fin d) (Fin d) ℂ, A*R+s • (R*X)=X ∧
      (Matrix.trace (X*R)).re = ∑ i, ∑ j,
        (hX.1.eigenvalues j ^ 2 / (hA.1.eigenvalues i+s*hX.1.eigenvalues j)) *
          Complex.normSq (overlap hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary i j) := by
  refine ⟨unitaryResolvent hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary
    hA.1.eigenvalues hX.1.eigenvalues s, ?_, ?_⟩
  · have h := unitaryResolvent_equation hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary
      hA.1.eigenvalues hX.1.eigenvalues s hA.eigenvalues_pos hX.eigenvalues_pos hs
    have ha := hA.1.spectral_theorem
    have hx := hX.1.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] at ha hx
    rw [← ha, ← hx] at h
    exact h
  · have h := trace_unitaryResolvent hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary
      hA.1.eigenvalues hX.1.eigenvalues s
    have hx := hX.1.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] at hx
    rw [← hx] at h
    exact h
end MatrixTailProof
end

section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace MatrixTailProof
noncomputable def resolventValue {d : ℕ} {A X : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosDef) (hX : X.PosDef) (s : ℝ) : ℝ :=
  ∑ i, ∑ j, (hX.1.eigenvalues j ^ 2 / (hA.1.eigenvalues i+s*hX.1.eigenvalues j)) *
    Complex.normSq (overlap hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary i j)

theorem resolvent_upper {d : ℕ} {A X : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosDef) (hX : X.PosDef) {s : ℝ} (hs : 0 ≤ s)
    (Y : Matrix (Fin d) (Fin d) ℂ) :
    2*(Matrix.trace (X*Y)).re-quadratic A X s Y ≤ resolventValue hA hX s := by
  obtain ⟨R,hR,hval⟩ := resolvent_certificate hA hX hs
  rw [quadratic_completion hA.1 hX.1 s hR Y]
  have hn := quadratic_nonneg hA hX hs (Y-R)
  change (Matrix.trace (X*R)).re = resolventValue hA hX s at hval
  linarith

theorem resolvent_attained {d : ℕ} {A X : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosDef) (hX : X.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    ∃ Y : Matrix (Fin d) (Fin d) ℂ,
      resolventValue hA hX s = 2*(Matrix.trace (X*Y)).re-quadratic A X s Y := by
  obtain ⟨R,hR,hval⟩ := resolvent_certificate hA hX hs
  refine ⟨R, ?_⟩
  have he := quadratic_completion hA.1 hX.1 s hR R
  simpa [quadratic, hval, resolventValue] using he.symm

theorem resolvent_joint_convex {d : ℕ} {A B X Y : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hX : X.PosDef) (hY : Y.PosDef)
    {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hs : 0 ≤ s) :
    resolventValue (posDef_mix hA hB ht ht1) (posDef_mix hX hY ht ht1) s ≤
      (1-t)*resolventValue hA hX s+t*resolventValue hB hY s := by
  obtain ⟨R,hr⟩ := resolvent_attained (posDef_mix hA hB ht ht1)
    (posDef_mix hX hY ht ht1) hs
  have ha := mul_le_mul_of_nonneg_left (resolvent_upper hA hX hs R) (sub_nonneg.mpr ht1)
  have hb := mul_le_mul_of_nonneg_left (resolvent_upper hB hY hs R) ht
  rw [hr]
  have he : 2*(Matrix.trace (((1-t) • X+t • Y)*R)).re-
      quadratic ((1-t) • A+t • B) ((1-t) • X+t • Y) s R =
      (1-t)*(2*(Matrix.trace (X*R)).re-quadratic A X s R)+
      t*(2*(Matrix.trace (Y*R)).re-quadratic B Y s R) := by
    simp only [quadratic, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [he]
  exact add_le_add ha hb
end MatrixTailProof
end

section
open MeasureTheory Filter Set
open scoped Topology
namespace MatrixTailProof

noncomputable def scalarResolvent (l m s : ℝ) : ℝ := l ^ 2 / (m + s * l) - l / (1 + s)

theorem scalarResolvent_continuousOn {l m : ℝ} (hl : 0 < l) (hm : 0 < m) :
    ContinuousOn (scalarResolvent l m) (Ici 0) := by
  apply ContinuousOn.sub
  · exact continuousOn_const.div (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
      (fun s hs => ne_of_gt (by have hs0 : 0 ≤ s := hs; positivity))
  · exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
      (fun s hs => ne_of_gt (by have hs0 : 0 ≤ s := hs; positivity))

theorem scalarResolvent_integral {l m R : ℝ} (hl : 0 < l) (hm : 0 < m) (hR : 0 ≤ R) :
    (∫ s in (0 : ℝ)..R, scalarResolvent l m s) =
      l * (Real.log (m + R * l) - Real.log m - Real.log (1 + R)) := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) R,
      HasDerivAt (fun t : ℝ => l * (Real.log (m + t*l) - Real.log (1+t)))
        (scalarResolvent l m s) s := by
    intro s hs
    have hs0 : 0 ≤ s := (uIcc_of_le hR ▸ hs).1
    have hm' : m+s*l ≠ 0 := ne_of_gt (by positivity)
    have hs' : 1+s ≠ 0 := ne_of_gt (by positivity)
    convert (((((hasDerivAt_id s).mul_const l).const_add m).log hm').sub
      (((hasDerivAt_id s).const_add 1).log hs')).const_mul l using 1 <;>
      first | rfl | (simp only [scalarResolvent, id_eq, one_mul]; ring)
  have hi : IntervalIntegrable (scalarResolvent l m) volume 0 R :=
    ((scalarResolvent_continuousOn hl hm).mono (by
      intro s hs; exact (uIcc_of_le hR ▸ hs).1)).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp only [zero_mul, add_zero, Real.log_one, sub_zero]
  ring

theorem scalarResolvent_limit {l m : ℝ} (hl : 0 < l) (hm : 0 < m) :
    Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..R, scalarResolvent l m s) atTop
      (𝓝 (l * (Real.log l - Real.log m))) := by
  have hi : Tendsto (fun R : ℝ => (1+R)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_const_nhds.add_atTop tendsto_id)
  have hr : Tendsto (fun R : ℝ => l+(m-l)*(1+R)⁻¹) atTop (𝓝 l) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hi)
  have ht := ((Real.continuousAt_log hl.ne').tendsto.comp hr).sub_const (Real.log m)
  apply Tendsto.congr' _ (ht.const_mul l)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [scalarResolvent_integral hl hm hR]
  have ha : 0 < m+R*l := by positivity
  have hb : 0 < 1+R := by positivity
  have he : l+(m-l)*(1+R)⁻¹ = (m+R*l)/(1+R) := by field_simp; ring
  dsimp only [Function.comp_def]
  rw [he, Real.log_div ha.ne' hb.ne']
  ring
end MatrixTailProof
end

section
open Matrix MatrixTail.Master
open scoped ComplexOrder MatrixOrder
namespace MatrixTailProof

theorem trace_spectral {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian) :
    (Matrix.trace X).re = ∑ j, hX.eigenvalues j := by
  conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

theorem scalar_klein {l m : ℝ} (hl : 0 < l) (hm : 0 < m) :
    l-m ≤ l*(Real.log l-Real.log m) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hl hm)
  rw [Real.log_div hl.ne' hm.ne', inv_div] at h
  have hh := mul_le_mul_of_nonneg_left h hl.le
  have he : l*(1-m/l)=l-m := by field_simp
  simpa only [he] using hh

theorem klein {d : ℕ} {X A : Matrix (Fin d) (Fin d) ℂ}
    (hX : X.PosDef) (hA : A.PosDef) :
    (Matrix.trace X).re - (Matrix.trace A).re ≤ entropy0 X A := by
  let C : Matrix.unitaryGroup (Fin d) ℂ := star hA.1.eigenvectorUnitary * hX.1.eigenvectorUnitary
  have hr (i : Fin d) : ∑ j, Complex.normSq (overlap hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary i j) = 1 :=
    unitary_row_normSq C i
  have hc (j : Fin d) : ∑ i, Complex.normSq (overlap hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary i j) = 1 :=
    unitary_col_normSq C j
  have hx : (∑ i, ∑ j, hX.1.eigenvalues j *
      Complex.normSq (overlap hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary i j)) =
      ∑ j, hX.1.eigenvalues j := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hc, mul_one]
  have ha : (∑ i, ∑ j, hA.1.eigenvalues i *
      Complex.normSq (overlap hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary i j)) =
      ∑ i, hA.1.eigenvalues i := by
    simp only [← Finset.mul_sum, hr, mul_one]
  rw [trace_spectral hX.1, trace_spectral hA.1, entropy_spectral hX.1 hA.1, ← hx, ← ha]
  simp only [← Finset.sum_sub_distrib, ← sub_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right (scalar_klein (hX.eigenvalues_pos j) (hA.eigenvalues_pos i))
    (Complex.normSq_nonneg _)
end MatrixTailProof
end

section
open Matrix MeasureTheory Filter Set
open scoped ComplexOrder MatrixOrder Topology
namespace MatrixTailProof
noncomputable def entropyIntegrand {d : ℕ} {X A : Matrix (Fin d) (Fin d) ℂ}
    (hX : X.PosDef) (hA : A.PosDef) (s : ℝ) : ℝ :=
  ∑ i, ∑ j, scalarResolvent (hX.1.eigenvalues j) (hA.1.eigenvalues i) s *
    Complex.normSq (overlap hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary i j)

theorem entropyIntegrand_eq {d : ℕ} {X A : Matrix (Fin d) (Fin d) ℂ}
    (hX : X.PosDef) (hA : A.PosDef) (s : ℝ) :
    entropyIntegrand hX hA s = resolventValue hA hX s-(Matrix.trace X).re/(1+s) := by
  unfold entropyIntegrand resolventValue scalarResolvent
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm, trace_spectral hX.1, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum]
  have hc := unitary_col_normSq (star hA.1.eigenvectorUnitary * hX.1.eigenvectorUnitary) j
  change (∑ i, Complex.normSq (overlap hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary i j)) = 1 at hc
  rw [hc, mul_one]

theorem entropyIntegrand_continuousOn {d : ℕ} {X A : Matrix (Fin d) (Fin d) ℂ}
    (hX : X.PosDef) (hA : A.PosDef) :
    ContinuousOn (entropyIntegrand hX hA) (Ici 0) := by
  apply continuousOn_finsetSum
  intro i hi
  apply continuousOn_finsetSum
  intro j hj
  exact (scalarResolvent_continuousOn (hX.eigenvalues_pos j) (hA.eigenvalues_pos i)).mul_const _

theorem entropyIntegral_limit {d : ℕ} {X A : Matrix (Fin d) (Fin d) ℂ}
    (hX : X.PosDef) (hA : A.PosDef) :
    Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..R, entropyIntegrand hX hA s) atTop
      (𝓝 (entropy0 X A)) := by
  rw [entropy_spectral hX.1 hA.1]
  have hh := tendsto_finsetSum Finset.univ (fun i hi =>
    tendsto_finsetSum Finset.univ (fun j hj =>
      (scalarResolvent_limit (hX.eigenvalues_pos j) (hA.eigenvalues_pos i)).mul_const
        (Complex.normSq (overlap hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary i j))))
  apply Tendsto.congr' _ hh
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have hi i j : IntervalIntegrable
      (fun s => scalarResolvent (hX.1.eigenvalues j) (hA.1.eigenvalues i) s *
        Complex.normSq (overlap hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary i j))
      volume 0 R :=
    (((scalarResolvent_continuousOn (hX.eigenvalues_pos j) (hA.eigenvalues_pos i)).mul_const _).mono (by intro s hs; exact (uIcc_of_le hR ▸ hs).1)).intervalIntegrable
  simp only [entropyIntegrand]
  have ho i : IntervalIntegrable
      (fun s => ∑ j, scalarResolvent (hX.1.eigenvalues j) (hA.1.eigenvalues i) s *
        Complex.normSq (overlap hA.1.eigenvectorUnitary hX.1.eigenvectorUnitary i j)) volume 0 R := by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => hi i j) using 1 <;>
      first | rfl | (ext s; simp)
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun i _ => ho i)]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun j _ => hi i j)]
  simp only [intervalIntegral.integral_mul_const]
end MatrixTailProof
end

section
open Matrix MeasureTheory Filter Set
open scoped ComplexOrder MatrixOrder Topology
namespace MatrixTailProof

theorem entropyIntegrand_convex {d : ℕ} {A B X Y : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hX : X.PosDef) (hY : Y.PosDef)
    {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hs : 0 ≤ s) :
    entropyIntegrand (posDef_mix hX hY ht ht1) (posDef_mix hA hB ht ht1) s ≤
      (1-t)*entropyIntegrand hX hA s+t*entropyIntegrand hY hB s := by
  simp only [entropyIntegrand_eq, Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h := resolvent_joint_convex hA hB hX hY ht ht1 hs
  convert sub_le_sub_right h (((1-t)*(Matrix.trace X).re+t*(Matrix.trace Y).re)/(1+s)) using 1; ring

theorem entropy_joint_convex {d : ℕ} {A B X Y : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hX : X.PosDef) (hY : Y.PosDef)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    entropy0 ((1-t) • X+t • Y) ((1-t) • A+t • B) ≤
      (1-t)*entropy0 X A+t*entropy0 Y B := by
  have hm := entropyIntegral_limit (posDef_mix hX hY ht ht1) (posDef_mix hA hB ht ht1)
  have hr := ((entropyIntegral_limit hX hA).const_mul (1-t)).add
    ((entropyIntegral_limit hY hB).const_mul t)
  apply le_of_tendsto_of_tendsto hm hr
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have hi {Z C : Matrix (Fin d) (Fin d) ℂ} (hZ : Z.PosDef) (hC : C.PosDef) :
      IntervalIntegrable (entropyIntegrand hZ hC) volume 0 R :=
    ((entropyIntegrand_continuousOn hZ hC).mono (by
      intro s hs; exact (uIcc_of_le hR ▸ hs).1)).intervalIntegrable
  have h := intervalIntegral.integral_mono_on hR
    (hi (posDef_mix hX hY ht ht1) (posDef_mix hA hB ht ht1))
    (((hi hX hA).const_mul (1-t)).add ((hi hY hB).const_mul t))
    (fun s hs => entropyIntegrand_convex hA hB hX hY ht ht1 hs.1)
  simpa only [intervalIntegral.integral_add ((hi hX hA).const_mul (1-t))
    ((hi hY hB).const_mul t), intervalIntegral.integral_const_mul] using h
end MatrixTailProof
end

section
open Matrix MatrixTail.Master
open scoped ComplexOrder MatrixOrder
namespace MatrixTailProof
noncomputable def variational {d : ℕ} (H A X : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (Matrix.trace (X*H)).re - entropy0 X A + (Matrix.trace X).re

theorem trace_variational_upper {d : ℕ} {H X : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) (hX : X.PosDef) :
    (Matrix.trace (X*H)).re - (Matrix.trace (X*mlog X)).re + (Matrix.trace X).re ≤ trExp H := by
  have h := klein hX (mexp_posDef hH)
  unfold entropy0 at h
  rw [mlog_mexp hH, mul_sub, Matrix.trace_sub, Complex.sub_re] at h
  change _ ≤ (Matrix.trace (mexp H)).re
  linarith

theorem variational_upper {d : ℕ} {H A X : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) (hX : X.PosDef) : variational H A X ≤ trExp (H+mlog A) := by
  have h := trace_variational_upper (hH.add (mlog_isHermitian A)) hX
  unfold variational entropy0
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [mul_add, Matrix.trace_add, Complex.add_re] at h
  linarith

theorem variational_attained {d : ℕ} {H A : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) :
    variational H A (mexp (H+mlog A)) = trExp (H+mlog A) := by
  unfold variational entropy0 trExp
  rw [mlog_mexp (hH.add (mlog_isHermitian A))]
  simp
end MatrixTailProof
end

section
open Matrix MatrixTail.Master
open scoped ComplexOrder MatrixOrder
namespace MatrixTailProof

theorem lieb_concave {d : ℕ} {H A B : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1-t)*trExp (H+mlog A)+t*trExp (H+mlog B) ≤
      trExp (H+mlog ((1-t) • A+t • B)) := by
  let X := mexp (H+mlog A)
  let Y := mexp (H+mlog B)
  have hX : X.PosDef := mexp_posDef (hH.add (mlog_isHermitian A))
  have hY : Y.PosDef := mexp_posDef (hH.add (mlog_isHermitian B))
  have he := entropy_joint_convex hA hB hX hY ht ht1
  have hu := variational_upper (A := (1-t) • A+t • B) hH (posDef_mix hX hY ht ht1)
  have ha : variational H A X=trExp (H+mlog A) := variational_attained hH
  have hb : variational H B Y=trExp (H+mlog B) := variational_attained hH
  have hm : (1-t)*variational H A X+t*variational H B Y ≤
      variational H ((1-t) • A+t • B) ((1-t) • X+t • Y) := by
    unfold variational
    simp only [add_mul, smul_mul_assoc, Matrix.trace_add, Matrix.trace_smul,
      Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    linarith
  rw [ha,hb] at hm
  exact hm.trans hu
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
open MatrixTail.Master
namespace MatrixTailProof
lemma full_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d n : ℕ} [NeZero d] (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hXm : ∀ k, Measurable (X k)) (hX : ∀ k ω, (X k ω).IsHermitian)
    (hI : iIndepFun X P) (t θ : ℝ) (hθ : 0 < θ)
    (hi : ∀ k, MatIntegrable P (fun ω => mexp (θ • X k ω))) :
    P.real {ω | t ≤ lambdaMax (∑ k, X k ω)} ≤
      Real.exp (-θ*t) * trExp (∑ k, mlog (mean P (fun ω => mexp (θ • X k ω)))) := by
  have hL : ∀ H : Matrix (Fin d) (Fin d) ℂ, H.IsHermitian → ConcaveOn ℝ (pdCone d) (liebFun H) := by
    intro H hH
    apply liebFun_concave
    intro A B hA hB s hs hs1
    exact lieb_concave hH hA hB hs hs1
  let Z : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ := fun k ω => θ • X k ω
  have hZm : ∀ k, Measurable (Z k) := fun k => (hXm k).const_smul θ
  have hZh : ∀ k ω, (Z k ω).IsHermitian := fun k ω => (hX k ω).smul (show IsSelfAdjoint θ from rfl)
  have hZi : iIndepFun Z P := hI.comp (fun _ A => θ • A) (fun _ => measurable_id.const_smul θ)
  have hc := finite_cgf hL Z hZm hZh hZi hi Finset.univ 0 (by simp [Matrix.IsHermitian])
  simp only [zero_add] at hc
  have he : (fun ω => trExp (∑ k, Z k ω)) = (fun ω => trExp (θ • ∑ k, X k ω)) := by
    funext ω
    rw [Finset.smul_sum]
  rw [he] at hc
  have hs : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω => isSelfAdjoint_sum _ (fun k _ => hX k ω)
  exact (matrix_laplace hs hθ hc.1 t).trans (mul_le_mul_of_nonneg_left hc.2 (Real.exp_pos _).le)
end MatrixTailProof
end

section
open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
namespace MatrixTail.Master

/-- **Theorem 3.6 (Master Tail Bound for Independent Sums).** Tropp, *User-Friendly Tail Bounds for Sums of
Random Matrices*, arXiv:1004.4389v7, p. 12, display (3.5): "Consider a finite sequence `{X_k}` of independent,
random, self-adjoint matrices. For all `t ∈ ℝ`,
`P{λmax(Σ_k X_k) ≥ t} ≤ inf_{θ>0} { e^{−θt} · tr exp(Σ_k log E e^{θX_k}) }`."

Proof on the page: "Substitute the subadditivity rule for matrix cgfs, Lemma 3.4, into the Laplace transform
bound, Proposition 3.1."

**Formalization Note.**
* The finite sequence is `X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ` (complex matrices, §2.1), each `X k`
  measurable and Hermitian at every outcome, jointly independent (`iIndepFun X P`) under a probability
  measure `P`; the dimension is `d ≥ 1` (`[NeZero d]`), since for `d = 0`, `λmax = sSup ∅ = 0` and the
  bound would fail at `t ≤ 0`.
* The infimum over `θ > 0` is stated as the bound for every `θ > 0` at which all the mgfs `E e^{θX_k}` exist
  (every entry of `e^{θX_k}` integrable, `MatIntegrable`: the §2.2 regularity made explicit). The paper admits
  non-existent mgfs (p. 9), for which the right side is `+∞`; since `P ≤ inf_θ F(θ)` iff `P ≤ F(θ)` for
  every `θ`, this reading is exact. No real-valued `⨅` is used (it would be `0` on a set unbounded below).
* `E` is the entrywise expectation `mean`; `exp`/`log` are `cfc Real.exp`/`cfc Real.log`; `tr exp(·)` is
  `trExp`; `λmax` is `lambdaMax`. -/
theorem proved_root {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d n : ℕ} [NeZero d] (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hX_meas : ∀ k, Measurable (X k)) (hX_herm : ∀ k ω, (X k ω).IsHermitian)
    (hX_indep : iIndepFun X P) :
    ∀ (t θ : ℝ), 0 < θ → (∀ k, MatIntegrable P (fun ω => mexp (θ • X k ω))) →
      P.real {ω | t ≤ lambdaMax (∑ k, X k ω)} ≤
        Real.exp (-θ * t) * trExp (∑ k, mlog (mean P (fun ω => mexp (θ • X k ω)))) := by
  intro t θ hθ hi
  exact MatrixTailProof.full_bound P X hX_meas hX_herm hX_indep t θ hθ hi

end MatrixTail.Master
end

open MeasureTheory ProbabilityTheory MatrixTail.Master

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d n : ℕ} [NeZero d] (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hX_meas : ∀ k, Measurable (X k)) (hX_herm : ∀ k ω, (X k ω).IsHermitian)
    (hX_indep : iIndepFun X P) :
    ∀ (t θ : ℝ), 0 < θ → (∀ k, MatIntegrable P (fun ω => mexp (θ • X k ω))) →
      P.real {ω | t ≤ lambdaMax (∑ k, X k ω)} ≤
        Real.exp (-θ * t) * trExp (∑ k, mlog (mean P (fun ω => mexp (θ • X k ω)))) := by
  exact MatrixTail.Master.proved_root P X hX_meas hX_herm hX_indep

theorem MatrixTail.Master.theorem3_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d n : ℕ} [NeZero d] (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hX_meas : ∀ k, Measurable (X k)) (hX_herm : ∀ k ω, (X k ω).IsHermitian)
    (hX_indep : iIndepFun X P) :
    ∀ (t θ : ℝ), 0 < θ → (∀ k, MatIntegrable P (fun ω => mexp (θ • X k ω))) →
      P.real {ω | t ≤ lambdaMax (∑ k, X k ω)} ≤
        Real.exp (-θ * t) * trExp (∑ k, mlog (mean P (fun ω => mexp (θ • X k ω)))) := by
  exact _root_.solution P X hX_meas hX_herm hX_indep
