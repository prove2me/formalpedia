-- Prove2me | solution 1 for OAI.KervaireHorizontalCurrent.integral_pullback_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:07:40.843281+00:00
-- url     : https://prove2.me/submissions/433689cc-19fa-456c-a9bf-60a72648afc9

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/CurrentPullback.lean:L241-L313
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireHorizontalCurrent.integral_pullback_constant. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Theorems.Thm_OAI_KervaireCurrentHomotopy_integral_eval_constant
import Theorems.Thm_OAI_KervaireCurrentPullback_contDiff_of_multilinear
import Theorems.Thm_OAI_KervaireUnitaryHaarCurrent_integral_liftField_eq_zero

-- ---- from OAI.GroupTheory.Kervaire.HaarCurrents ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology

namespace KervaireHaarFlow

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

end KervaireHaarFlow

open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff

namespace KervaireClosedCurrent

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end KervaireClosedCurrent

namespace KervaireCurrentHomotopy
-- [generator] trimmed: open KervaireClosedCurrent KervaireHaarFlow VectorField ContinuousAlternatingMap
open KervaireHaarFlow VectorField ContinuousAlternatingMap
open scoped ContDiff

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

end KervaireCurrentHomotopy

namespace KervaireHaarFlow

open NormedSpace
open scoped ContDiff

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  [StarRing B] [ContinuousStar B] [StarModule ℝ B]

attribute [local instance] OAI.KervaireHaarFlow.instNormedAlgebraRat_oAI
variable [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

end KervaireHaarFlow

namespace KervaireUnitaryHaarCurrent
open MeasureTheory VectorField
open scoped ContDiff
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

lemma bracket_lift (a b : B) (p : ℝ × B) :
    lieBracket ℝ (liftField a) (liftField b) p = liftField (a*b-b*a) p := by
  simp only [lieBracket, ContinuousLinearMap.fderiv, liftField_apply, Prod.sub_def, sub_self]
  congr 1
  noncomm_ring

lemma bracket_time_lift (a : B) (p : ℝ × B) :
    lieBracket ℝ (fun _ : ℝ × B ↦ (1,0)) (liftField a) p = 0 := by
  simp [lieBracket]

variable [CompleteSpace B] [StarRing B] [ContinuousStar B] [StarModule ℝ B]
  [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

end KervaireUnitaryHaarCurrent

namespace KervaireCompactUnitary
variable {B : Type*} [CStarAlgebra B] [FiniteDimensional ℂ B]

end KervaireCompactUnitary

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.CurrentPullback ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff

namespace KervaireCurrentPullback

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Smoothness of pullback as an operation on smooth forms and smooth differentials. -/
lemma contDiff_compLinear {n : ℕ} [FiniteDimensional ℝ F] [FiniteDimensional ℝ H]
    {f : E → G [⋀^Fin n]→L[ℝ] H} {g : E → F →L[ℝ] G}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x ↦ (f x).compContinuousLinearMap (g x)) := by
  apply contDiff_of_multilinear
  exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n ↦ F) (fun _ ↦ G) H).contDiff.comp (contDiff_pi.mpr fun _ ↦ hg)).clm_apply
      ((toContinuousMultilinearMapCLM ℝ : (G [⋀^Fin n]→L[ℝ] H) →L[ℝ] _).contDiff.comp hf)

lemma contDiff_pullback {n : ℕ} [FiniteDimensional ℝ E] [FiniteDimensional ℝ H]
    {f : E → F} {form : F → F [⋀^Fin n]→L[ℝ] H}
    (hf : ContDiff ℝ ∞ f) (hform : ContDiff ℝ ∞ form) :
    ContDiff ℝ ∞ (fun x ↦ (form (f x)).compContinuousLinearMap (fderiv ℝ f x)) :=
  contDiff_compLinear (hform.comp hf) (hf.fderiv_right (by simp))

/-- An alternating form vanishes on more vectors than the dimension of their common subspace. -/
lemma eval_eq_zero_of_subspace {n : ℕ} (L : Submodule ℝ F) [FiniteDimensional ℝ L]
    (hL : Module.finrank ℝ L < n) (form : F [⋀^Fin n]→L[ℝ] ℝ)
    (v : Fin n → F) (hv : ∀ i, v i ∈ L) : form v = 0 := by
  let w : Fin n → L := fun i ↦ ⟨v i, hv i⟩
  have hdep : ¬ LinearIndependent ℝ w := by
    intro h
    have hh := h.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hh
    omega
  exact (form.toAlternatingMap.compLinearMap L.subtype).map_linearDependent w hdep

/-- Pullbacks are closed on frames whose images lie in a subspace of the target dimension. -/
lemma extDeriv_pullback_eval_eq_zero {n : ℕ} {f : E → F}
    {form : F → F [⋀^Fin n]→L[ℝ] ℝ} (hf : ContDiff ℝ ∞ f) (hform : ContDiff ℝ ∞ form)
    (x : E) (v : Fin (n+1) → E) (L : Submodule ℝ F) [FiniteDimensional ℝ L]
    (hL : Module.finrank ℝ L ≤ n) (hv : ∀ i, fderiv ℝ f x (v i) ∈ L) :
    extDeriv (fun x ↦ (form (f x)).compContinuousLinearMap (fderiv ℝ f x)) x v = 0 := by
  rw [extDeriv_pullback (hform.differentiable (by simp) _) hf.contDiffAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)]
  exact eval_eq_zero_of_subspace L (by omega) (extDeriv form (f x)) _ hv

end KervaireCurrentPullback

open MeasureTheory NormedSpace
open scoped ContDiff

namespace KervaireUnitaryTangent

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
  [StarRing B] [ContinuousStar B] [StarModule ℝ B]

omit [ContinuousStar B] in
lemma mem_tangent (u : unitary B) (d : B)
    (hd : star (u : B) * d ∈ skewAdjoint.submodule ℝ B) : d ∈ tangent u := by
  refine ⟨star (u : B)*d,hd,?_⟩
  change (u : B)*(star (u : B)*d) = d
  rw [← mul_assoc, u.property.2, one_mul]

/-- Differentiating the actual unitary identity gives a tangent vector. -/
lemma hasDerivAt_mem_tangent {f : ℝ → B} {d : B} {t : ℝ}
    (hd : HasDerivAt f d t) (hf : ∀ s, f s ∈ unitary B) :
    d ∈ tangent ⟨f t, hf t⟩ := by
  apply mem_tangent
  have heq : (fun s ↦ star (f s) * f s) = fun _ : ℝ ↦ (1 : B) :=
    funext fun s ↦ (hf s).1
  have hprod := hd.star.mul hd
  change HasDerivAt (fun s ↦ star (f s) * f s) _ t at hprod
  rw [heq] at hprod
  have hz := hprod.unique (hasDerivAt_const t (1 : B))
  change star (star (f t)*d) = -(star (f t)*d)
  rw [star_mul, star_star]
  exact eq_neg_of_add_eq_zero_left hz

omit [ContinuousStar B] in
lemma finrank_tangent_le [FiniteDimensional ℝ B] (u : unitary B) :
    Module.finrank ℝ (tangent u) ≤ Module.finrank ℝ (skewAdjoint.submodule ℝ B) :=
  Submodule.finrank_map_le _ _

/-- A Fréchet differential is tangent along any genuine unitary curve. -/
lemma fderiv_mem_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → B} {x v : E} (hf : DifferentiableAt ℝ f x)
    (c : ℝ → E) (hc : c 0 = x) (hd : HasDerivAt c v 0)
    (hu : ∀ t, f (c t) ∈ unitary B) :
    fderiv ℝ f x v ∈ tangent ⟨f x, hc ▸ hu 0⟩ := by
  have hh := ((hc.symm ▸ hf.hasFDerivAt).comp_hasDerivAt 0 hd)
  simpa only [Function.comp_apply, hc] using hasDerivAt_mem_tangent hh hu

end KervaireUnitaryTangent

open Module Set ContinuousAlternatingMap
namespace KervaireAlternatingSpan
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma eval_cons_eq_zero {n : ℕ} (form : E [⋀^Fin (n+1)]→L[ℝ] F)
    (v : Fin n → E) (w : E) (hw : w ∈ Submodule.span ℝ (range v)) :
    form (Fin.cons w v) = 0 := by
  apply form.toAlternatingMap.map_linearDependent
  rw [linearIndependent_finCons]
  exact fun h ↦ h.2 hw

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma removeNth_removeNth_range {n : ℕ} (v : Fin (n+2) → E)
    (i j : Fin (n+1)) (hij : i ≤ j) :
    v '' {l | l ≠ i.castSucc ∧ l ≠ j.succ} =
      range (j.removeNth (i.castSucc.removeNth v)) := by
  ext x
  simp only [mem_image, mem_ofPred_eq, mem_range, Fin.removeNth_apply]
  constructor
  · rintro ⟨l, ⟨hli,hlj⟩,rfl⟩
    obtain ⟨a,rfl⟩ := (Fin.exists_succAbove_eq_iff.mpr hli)
    have ha : a ≠ j := by
      intro h
      subst a
      apply hlj
      exact Fin.succAbove_of_le_castSucc _ _ hij
    obtain ⟨b,rfl⟩ := Fin.exists_succAbove_eq_iff.mpr ha
    exact ⟨b,rfl⟩
  · rintro ⟨a,rfl⟩
    refine ⟨i.castSucc.succAbove (j.succAbove a), ⟨Fin.succAbove_ne _ _, ?_⟩,rfl⟩
    rw [← Fin.succAbove_of_le_castSucc i.castSucc j hij]
    exact fun h ↦ Fin.succAbove_ne _ _ (Fin.succAbove_right_injective h)

lemma eval_bracket_eq_zero {n : ℕ} (form : E [⋀^Fin (n+1)]→L[ℝ] F)
    (v : Fin (n+2) → E) (c : Fin (n+2) → ℝ)
    (i j : Fin (n+1)) (hij : i ≤ j)
    (hi : c i.castSucc = 0) (hj : c j.succ = 0) :
    form (Fin.cons (∑ l, c l • v l) (j.removeNth (i.castSucc.removeNth v))) = 0 := by
  apply eval_cons_eq_zero
  rw [← removeNth_removeNth_range v i j hij]
  apply Submodule.sum_mem
  intro l _
  by_cases hli : l = i.castSucc
  · subst l
    simp [hi]
  by_cases hlj : l = j.succ
  · subst l
    simp [hj]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l,⟨hli,hlj⟩,rfl⟩)

end KervaireAlternatingSpan

namespace KervaireHorizontalCurrent
open MeasureTheory ContinuousAlternatingMap VectorField
open KervaireUnitaryHaarCurrent KervaireUnitaryTangent KervaireCurrentPullback
open scoped ContDiff
variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
  [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [CompactSpace (unitary B)] [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

attribute [local instance] OAI.KervaireHorizontalCurrent.instNormedAlgebraRat_oAI
omit [FiniteDimensional ℝ B] [FiniteDimensional ℝ C] [CompactSpace (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)] in
lemma time_tangent {f : (ℝ × B) → C} (hf : ContDiff ℝ ∞ f)
    (hu : ∀ t (x : unitary B), f (t,(x : B)) ∈ unitary C)
    (t : ℝ) (x : unitary B) :
    fderiv ℝ f (t,(x : B)) (1,0) ∈ tangent ⟨f (t,(x : B)),hu t x⟩ := by
  apply fderiv_mem_tangent (hf.differentiable (by simp) _) (fun s ↦ (t+s,(x : B))) (by simp)
  · convert ((hasDerivAt_const 0 t).add (hasDerivAt_id 0)).prodMk (hasDerivAt_const 0 (x : B)) using 1 <;> first | rfl | simp
  · intro s
    exact hu (t+s) x

omit [FiniteDimensional ℝ B] [FiniteDimensional ℝ C] [CompactSpace (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)] in
lemma horizontal_tangent {f : (ℝ × B) → C} (hf : ContDiff ℝ ∞ f)
    (hu : ∀ t (x : unitary B), f (t,(x : B)) ∈ unitary C)
    (t : ℝ) (x : unitary B) (a : skewAdjoint.submodule ℝ B) :
    fderiv ℝ f (t,(x : B)) (0,(x : B)*(a : B)) ∈ tangent ⟨f (t,(x : B)),hu t x⟩ := by
  apply fderiv_mem_tangent (hf.differentiable (by simp) _)
    (fun s ↦ (t,(x : B)*NormedSpace.exp (s • (a : B)))) (by simp)
  · simpa using (hasDerivAt_const (0 : ℝ) t).prodMk ((hasDerivAt_const (0 : ℝ) (x : B)).mul
      (hasDerivAt_exp_smul_const (a : B) (0 : ℝ)))
  · intro s
    exact hu t (x * KervaireHaarFlow.expFlow a s)

/-- Haar current homotopy invariance in a horizontal frame. The bracket condition is
an explicit infinitesimal condition (not a topological-degree assumption). -/
lemma integral_pullback_constant {n : ℕ} (a : Fin (n+1) → skewAdjoint.submodule ℝ B)
    {f : (ℝ × B) → C} (hf : ContDiff ℝ ∞ f)
    (hu : ∀ t (x : unitary B), f (t,(x : B)) ∈ unitary C)
    (hdim : Module.finrank ℝ (skewAdjoint.submodule ℝ C) ≤ n+1)
    (hbr : ∀ t (x : unitary B) (i j : Fin (n+1)), i ≠ j →
      ∃ c : Fin (n+1) → ℝ, c i = 0 ∧ c j = 0 ∧
        fderiv ℝ f (t,(x : B)) (0,(x : B)*((a i : B)*(a j : B)-(a j : B)*(a i : B))) =
          ∑ l, c l • fderiv ℝ f (t,(x : B)) (0,(x : B)*(a l : B)))
    (form : C → C [⋀^Fin (n+1)]→L[ℝ] ℝ) (hform : ContDiff ℝ ∞ form) (t₀ t₁ : ℝ) :
    (∫ x : unitary B, form (f (t₀,(x : B)))
        (fun i ↦ fderiv ℝ f (t₀,(x : B)) (0,(x : B)*(a i : B))) ∂μ) =
    (∫ x : unitary B, form (f (t₁,(x : B)))
        (fun i ↦ fderiv ℝ f (t₁,(x : B)) (0,(x : B)*(a i : B))) ∂μ) := by
  let V : Fin (n+2) → (ℝ × B) → (ℝ × B) :=
    Fin.cons (fun _ ↦ (1,0)) (fun i ↦ liftField (a i : B))
  let pull : (ℝ × B) → (ℝ × B) [⋀^Fin (n+1)]→L[ℝ] ℝ :=
    fun p ↦ (form (f p)).compContinuousLinearMap (fderiv ℝ f p)
  have hV : ∀ i, ContDiff ℝ ∞ (V i) := by
    intro i
    refine Fin.cases contDiff_const (fun j ↦ ?_) i
    exact (liftField (a j : B)).contDiff
  have hzero : ∀ p, V 0 p = (1,0) := fun _ ↦ rfl
  have hdiv (t : ℝ) (i : Fin (n+2)) (hi : i ≠ 0) (g : (ℝ × B) → ℝ)
      (hg : ContDiff ℝ ∞ g) :
      (∫ x : unitary B, fderiv ℝ g (t,(x : B)) (V i (t,(x : B))) ∂μ) = 0 := by
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq.mpr hi
    exact integral_liftField_eq_zero t hg (a j)
  have hclosed (t : ℝ) (x : unitary B) :
      extDeriv pull (t,(x : B)) (fun l ↦ V l (t,(x : B))) = 0 := by
    apply extDeriv_pullback_eval_eq_zero hf hform _ _ (tangent ⟨_,hu t x⟩)
      ((finrank_tangent_le _).trans hdim)
    intro i
    refine Fin.cases (time_tangent hf hu t x) (fun j ↦ ?_) i
    exact horizontal_tangent hf hu t x (a j)
  have hbracket (t : ℝ) (x : unitary B) (i j : Fin (n+1)) (hij : i ≤ j) :
      pull (t,(x : B)) (Matrix.vecCons (lieBracket ℝ (V i.castSucc) (V j.succ) (t,(x : B)))
        (j.removeNth (i.castSucc.removeNth (fun l ↦ V l (t,(x : B)))))) = 0 := by
    by_cases hi : i = 0
    · subst i
      apply (pull (t,(x : B))).map_coord_zero 0
      change lieBracket ℝ (fun _ : ℝ × B ↦ (1,0)) (liftField (a j : B)) (t,(x : B)) = 0
      exact bracket_time_lift _ _
    · obtain ⟨k,rfl⟩ := Fin.exists_succ_eq.mpr hi
      have hkj : k.castSucc ≠ j := by
        intro heq
        have hh := Fin.le_iff_val_le_val.mp hij
        simp only [← heq, Fin.val_succ, Fin.val_castSucc] at hh
        omega
      obtain ⟨c,hci,hcj,hc⟩ := hbr t x k.castSucc j hkj
      let w : Fin (n+2) → C := fun l ↦ fderiv ℝ f (t,(x : B)) (V l (t,(x : B)))
      let c' : Fin (n+2) → ℝ := Fin.cons 0 c
      have hcoeff : fderiv ℝ f (t,(x : B))
          (lieBracket ℝ (V k.succ.castSucc) (V j.succ) (t,(x : B))) =
            ∑ l, c' l • w l := by
        rw [show V k.succ.castSucc = liftField (a k.castSucc : B) from rfl,
          show V j.succ = liftField (a j : B) from rfl, bracket_lift, liftField_apply, hc]
        simp only [c', Fin.sum_univ_succ, Fin.cons_zero, zero_smul, Fin.cons_succ, zero_add]
        rfl
      have hz := KervaireAlternatingSpan.eval_bracket_eq_zero (form (f (t,(x : B)))) w
        c' k.succ j hij (by exact hci) (by exact hcj)
      change (form (f (t,(x : B)))) _ = 0
      convert hz using 1
      congr 1
      funext l
      refine Fin.cases ?_ (fun l ↦ ?_) l
      · exact hcoeff
      · rfl
  have hh := KervaireCurrentHomotopy.integral_eval_constant (μ := μ)
    (e := fun x : unitary B ↦ (x : B)) continuous_subtype_val
    (hf := contDiff_pullback hf hform) hV hzero hdiv hbracket hclosed t₀ t₁
  exact hh

end KervaireHorizontalCurrent

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireHorizontalCurrent
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open MeasureTheory ContinuousAlternatingMap VectorField
open KervaireUnitaryHaarCurrent KervaireUnitaryTangent KervaireCurrentPullback
open scoped ContDiff
attribute [local instance] OAI.KervaireHorizontalCurrent.instNormedAlgebraRat_oAI


theorem solution : type_of% @_root_.OAI.KervaireHorizontalCurrent.integral_pullback_constant := @_root_.OAI.KervaireHorizontalCurrent.integral_pullback_constant
