-- Prove2me | solution 1 for OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:21:22.776594+00:00
-- url     : https://prove2.me/submissions/a3d9640d-d828-4e6b-805c-c5357bf426d0

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C008
import Theorems.Thm_OAI_ScalarConductivity_PhysicalFiniteEndingData_corrected_block_smooth_green
import Theorems.Thm_OAI_ScalarConductivity_PhysicalFiniteEndingData_corrected_pair_representative
import Theorems.Thm_OAI_ScalarConductivity_complete_physical_attachment
import Theorems.Thm_OAI_ScalarConductivity_finite_field_scalarization
import Theorems.Thm_OAI_ScalarConductivity_fullAttachedEnd_smooth_green_neg
import Theorems.Thm_OAI_ScalarConductivity_fullAttachedEnd_smooth_green_pos

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_VariationalDN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

lemma half_harmonic_eq_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y = 2) : ((1 / 2 : ℝ) / x + (1 - 1 / 2) / y)⁻¹ = x * y := by
  have h : (1 / 2 : ℝ) / x + (1 - 1 / 2) / y = (x * y)⁻¹ := by
    field_simp
    nlinarith
  rw [h, inv_inv]

lemma coordinateJoin_half_smul (i : Fin 3) (v : DiagonalTriple) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y = 2) :
    coordinateJoin i (1/2) (x • v) (y • v) =
      fun j => if j = i then x * y * v j else v j := by
  ext j
  by_cases hji : j = i
  · simp only [coordinateJoin, hji, ite_true, Pi.smul_apply, smul_eq_mul]
    have hden : (1 / 2 : ℝ) / (x * v j) + (1 - 1 / 2) / (y * v j) =
        ((1 / 2 : ℝ) / x + (1 - 1 / 2) / y) / v j := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hji] at hden
    rw [hden, div_eq_mul_inv, mul_inv_rev, inv_inv, half_harmonic_eq_mul hx hy hxy]
    ring
  · simp only [coordinateJoin, hji, ite_false, Pi.smul_apply, smul_eq_mul]
    calc
      (1 / 2 : ℝ) * (x * v j) + (1 - 1 / 2) * (y * v j) = (x + y) / 2 * v j := by ring
      _ = v j := by rw [hxy]; ring

lemma productFactor_spec {M : ℝ} (hM : 0 < M) (α : DiagonalTriple) (i : Fin 3)
    (hα : 0 < α i ∧ α i < M) :
    0 < productFactorMinus M α i ∧ 0 < productFactorPlus M α i ∧
    productFactorMinus M α i + productFactorPlus M α i = 2 ∧
    productFactorMinus M α i * productFactorPlus M α i = α i / M := by
  have hq : 0 < α i / M := div_pos hα.1 hM
  have hq1 : α i / M < 1 := (div_lt_one hM).2 hα.2
  have hs0 := Real.sqrt_nonneg (1 - α i / M)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 - α i / M by linarith)
  dsimp [productFactorMinus, productFactorPlus]
  constructor
  · nlinarith
  constructor
  · linarith
  constructor
  · ring
  · nlinarith

lemma IsFiniteLaminate.half_smul {a b : ℝ} (i : Fin 3) (v : DiagonalTriple)
    {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y = 2)
    (hxl : IsFiniteLaminate a b (x • v)) (hyl : IsFiniteLaminate a b (y • v)) :
    IsFiniteLaminate a b (fun j => if j = i then x * y * v j else v j) := by
  rw [← coordinateJoin_half_smul i v hx hy hxy]
  exact IsFiniteLaminate.join i (1/2) (by norm_num) (by norm_num) hxl hyl

theorem product_eight_leaf_laminate {a b M : ℝ} (x y : Fin 3 → ℝ)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (hsum : ∀ i, x i + y i = 2)
    (hleaf : ∀ t₀ t₁ t₂ : ℝ, (t₀ = x 0 ∨ t₀ = y 0) →
      (t₁ = x 1 ∨ t₁ = y 1) → (t₂ = x 2 ∨ t₂ = y 2) →
      a < M * t₀ * t₁ * t₂ ∧ M * t₀ * t₁ * t₂ < b) :
    IsFiniteLaminate a b (fun i => M * x i * y i) := by
  have h₀ (t₁ t₂ : ℝ) (ht₁ : t₁ = x 1 ∨ t₁ = y 1)
      (ht₂ : t₂ = x 2 ∨ t₂ = y 2) :
      IsFiniteLaminate a b ![M * x 0 * y 0 * t₁ * t₂, M * t₁ * t₂, M * t₁ * t₂] := by
    let v : DiagonalTriple := fun _ => M * t₁ * t₂
    have hp : IsFiniteLaminate a b (x 0 • v) := by
      have hh := hleaf (x 0) t₁ t₂ (Or.inl rfl) ht₁ ht₂
      change IsFiniteLaminate a b (fun _ => x 0 * (M * t₁ * t₂))
      convert IsFiniteLaminate.scalar (M * x 0 * t₁ * t₂) hh.1 hh.2 using 1
      all_goals try with_reducible_and_instances rfl
      ext j
      ring
    have hm : IsFiniteLaminate a b (y 0 • v) := by
      have hh := hleaf (y 0) t₁ t₂ (Or.inr rfl) ht₁ ht₂
      change IsFiniteLaminate a b (fun _ => y 0 * (M * t₁ * t₂))
      convert IsFiniteLaminate.scalar (M * y 0 * t₁ * t₂) hh.1 hh.2 using 1
      all_goals try with_reducible_and_instances rfl
      ext j
      ring
    convert IsFiniteLaminate.half_smul 0 v (hx 0) (hy 0) (hsum 0) hp hm using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
  have h₁ (t₂ : ℝ) (ht₂ : t₂ = x 2 ∨ t₂ = y 2) :
      IsFiniteLaminate a b ![M * x 0 * y 0 * t₂, M * x 1 * y 1 * t₂, M * t₂] := by
    let v : DiagonalTriple := ![M * x 0 * y 0 * t₂, M * t₂, M * t₂]
    have hp : IsFiniteLaminate a b (x 1 • v) := by
      convert h₀ (x 1) t₂ (Or.inl rfl) ht₂ using 1
      all_goals try with_reducible_and_instances rfl
      ext j
      fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
    have hm : IsFiniteLaminate a b (y 1 • v) := by
      convert h₀ (y 1) t₂ (Or.inr rfl) ht₂ using 1
      all_goals try with_reducible_and_instances rfl
      ext j
      fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
    convert IsFiniteLaminate.half_smul 1 v (hx 1) (hy 1) (hsum 1) hp hm using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
  let v : DiagonalTriple := ![M * x 0 * y 0, M * x 1 * y 1, M]
  have hp : IsFiniteLaminate a b (x 2 • v) := by
    convert h₁ (x 2) (Or.inl rfl) using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
  have hm : IsFiniteLaminate a b (y 2 • v) := by
    convert h₁ (y 2) (Or.inr rfl) using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
  convert IsFiniteLaminate.half_smul 2 v (hx 2) (hy 2) (hsum 2) hp hm using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  fin_cases j <;> simp [v, mul_comm, mul_left_comm]

theorem uniform_laminate_coverage {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C) :
    0 < laminateLower c C ∧ laminateLower c C < laminateUpper C ∧
    ∀ α : DiagonalTriple, (∀ i, c ≤ α i ∧ α i ≤ C) →
      IsFiniteLaminate (laminateLower c C) (laminateUpper C) α := by
  let M := 2 * C
  let ℓ := 1 - Real.sqrt (1 - c / M)
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  have hM : 0 < M := by dsimp [M]; positivity
  have hcM : c < M := by dsimp [M]; linarith
  have hℓ : 0 < ℓ :=
    (productFactor_spec hM (fun _ => c) 0 ⟨hc, hcM⟩).1
  have hℓ1 : ℓ ≤ 1 := by dsimp [ℓ]; linarith [Real.sqrt_nonneg (1 - c / M)]
  have hℓ3 : ℓ ^ 3 ≤ 1 := by
    calc ℓ ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hℓ.le hℓ1 3
         _ = 1 := by norm_num
  have hbase : 0 < M * ℓ ^ 3 := mul_pos hM (pow_pos hℓ 3)
  change 0 < M * ℓ ^ 3 / 2 ∧ M * ℓ ^ 3 / 2 < 16 * M ∧ _
  refine ⟨by positivity, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hℓ3 hM.le]
  intro α hα
  let x := productFactorMinus M α
  let y := productFactorPlus M α
  have hspec (i : Fin 3) : 0 < x i ∧ 0 < y i ∧ x i + y i = 2 ∧ x i * y i = α i / M := by
    apply productFactor_spec hM α i
    constructor
    · exact lt_of_lt_of_le hc (hα i).1
    · dsimp [M]
      linarith [(hα i).2]
  have hx (i : Fin 3) : ℓ ≤ x i ∧ x i ≤ 2 := by
    dsimp [ℓ, x, productFactorMinus]
    constructor
    · have hh : 1 - α i / M ≤ 1 - c / M := by
        linarith [div_le_div_of_nonneg_right (hα i).1 hM.le]
      linarith [Real.sqrt_le_sqrt hh]
    · linarith [Real.sqrt_nonneg (1 - α i / M)]
  have hy (i : Fin 3) : ℓ ≤ y i ∧ y i ≤ 2 := by
    constructor
    · calc ℓ ≤ 1 := hℓ1
           _ ≤ y i := by
             dsimp [y, productFactorPlus]
             linarith [Real.sqrt_nonneg (1 - α i / M)]
    · have hs := hspec i
      linarith [hs.1, hs.2.2.1]
  have heq : (fun i => M * x i * y i) = α := by
    ext i
    rw [mul_assoc, (hspec i).2.2.2]
    exact mul_div_cancel₀ _ hM.ne'
  rw [← heq]
  apply product_eight_leaf_laminate x y (fun i => (hspec i).1.ne')
    (fun i => (hspec i).2.1.ne') (fun i => (hspec i).2.2.1)
  intro t₀ t₁ t₂ ht₀ ht₁ ht₂
  have hb₀ : ℓ ≤ t₀ ∧ t₀ ≤ 2 := ht₀.elim (fun h => h ▸ hx 0) (fun h => h ▸ hy 0)
  have hb₁ : ℓ ≤ t₁ ∧ t₁ ≤ 2 := ht₁.elim (fun h => h ▸ hx 1) (fun h => h ▸ hy 1)
  have hb₂ : ℓ ≤ t₂ ∧ t₂ ≤ 2 := ht₂.elim (fun h => h ▸ hx 2) (fun h => h ▸ hy 2)
  have ht₀0 : 0 ≤ t₀ := hℓ.le.trans hb₀.1
  have ht₁0 : 0 ≤ t₁ := hℓ.le.trans hb₁.1
  have ht₂0 : 0 ≤ t₂ := hℓ.le.trans hb₂.1
  have hlo : M * ℓ ^ 3 ≤ M * t₀ * t₁ * t₂ := by
    calc M * ℓ ^ 3 = M * ℓ * ℓ * ℓ := by ring
         _ ≤ M * t₀ * t₁ * t₂ := by gcongr <;> linarith
  have hhi : M * t₀ * t₁ * t₂ ≤ 8 * M := by
    calc M * t₀ * t₁ * t₂ ≤ M * 2 * 2 * 2 := by gcongr <;> linarith
         _ = 8 * M := by ring
  change M * ℓ ^ 3 / 2 < M * t₀ * t₁ * t₂ ∧ M * t₀ * t₁ * t₂ < 16 * M
  constructor <;> nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma sourcePhysicalCoordinates_right {y : Fin 3 → ℝ}
    (ht : sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100)) :
    sourceAngularCollar (sourceCollarTime y) (sourcePhysicalAngles y)=y := by
  obtain ⟨i,j,a,b,ha,hb,he⟩ := sourceCollarPiece_cover_extended
    (sourceRadial_pos_of_time ht.1) (by linarith [ht.2])
  have he' : sourceAngularCollar (sourceCollarTime y)
      (torusAngles (sourceFaceAngles i j ![sourceCollarTime y,a,b]))=y :=
    (sourceFaceAngles_physical i j ha hb).trans he
  have hinv := sourcePhysicalAngles_angular ht
    (torusAngles (sourceFaceAngles i j ![sourceCollarTime y,a,b]))
  rw [he'] at hinv
  rw [hinv]
  exact he'

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_BoundedMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem boundedMultiplier_apply_ae {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂μ, |a x| ≤ C) (f : Lp E 2 μ) :
    (boundedMultiplier μ a ha C hC haC f : α → E) =ᵐ[μ] fun x => a x • f x := by
  change (((boundedMultiplier_memLp μ a ha C haC f).toLp _) : α → E) =ᵐ[μ] _
  exact MemLp.coeFn_toLp _

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CompactLipschitzH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

theorem compact_lipschitz_H1 {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) {R : ℝ} (hR : R<3)
    (hs : ∀ x, R<‖x‖ → f x=0) :
    ∃ u : H1, u∈H10 ∧ (∀ᵐ x ∂ballMeasure,
      weakValue u x=f x ∧ ∀ i : Fin 3,
        weakGradient u x i=lineDeriv ℝ f x (EuclideanSpace.single i 1)) := by
  have hm : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport (bounded_support_compact hs)
  have hd (i : Fin 3) := lipschitz_lineDeriv_memLp hf hs (EuclideanSpace.single i 1)
  let F : Fin 4 → WholeL2 := Fin.cases (hm.toLp f)
    (fun i => (hd i).toLp (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)))
  have hv : (F 0 : R3 → ℝ)=ᵐ[volume] f := hm.coeFn_toLp
  have hg (i : Fin 3) : (F i.succ : R3 → ℝ)=ᵐ[volume]
      (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)) := (hd i).coeFn_toLp
  have hw (i : Fin 3) : WeakL2Direction (F 0) (F i.succ) (EuclideanSpace.single i 1) :=
    (lipschitz_weakDirection hf _).congr hv (hg i)
  obtain ⟨u,hu,he⟩ := compact_weak_H1 F hw hR (by
    filter_upwards [hv] with x hx
    intro hn
    exact hx.trans (hs x hn))
  refine ⟨u,hu,?_⟩
  have hv' := hv.filter_mono (ae_mono (Measure.restrict_le_self (s := ball)))
  have hg' := (ae_all_iff.mpr hg).filter_mono (ae_mono (Measure.restrict_le_self (s := ball)))
  filter_upwards [he,hv',hg'] with x hx hy hz
  exact ⟨hx.1.trans hy,fun i => (hx.2 i).trans (hz i)⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildTransportFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma childTransportComponentCLM_ae_of_ae (k : Fin 2) (z : JetSpace)
    (f : (Fin 3 → ℝ) → JetFiber) (he : ballWholePiJetCLM z=ᵐ[volume] f) (i : Fin 4) :
    childTransportComponentCLM k i z=ᵐ[volume] (fun y => Fin.cases
      (f ((sourceChildHomeomorph (actualChildSign k)).symm y) 0)
      (fun j => sourceScale⁻¹*f ((sourceChildHomeomorph (actualChildSign k)).symm y) (childAxis j).succ) i) := by
  have hc (j : Fin 4) : ballWholePiComponentCLM j z=ᵐ[volume] (fun y => f y j) := by
    filter_upwards [ballWholePiComponentCLM_ae j z,he] with y hi hy
    rw [hi,hy]
  have hp (j : Fin 4) := (sourceChildPushforwardCLM_ae (actualChildSign k) (ballWholePiComponentCLM j z)).trans
    ((sourceChildInverse_quasi _).ae_eq_comp (hc j))
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hp 0
  · apply (Lp.coeFn_smul _ _).trans
    filter_upwards [hp (childAxis j).succ] with y hy
    exact congrArg (fun t : ℝ => sourceScale⁻¹*t) hy

lemma childTransportJetCLM_ae_of_ae (k : Fin 2) (z : JetSpace)
    (f : (Fin 3 → ℝ) → JetFiber) (he : ballWholePiJetCLM z=ᵐ[volume] f) :
    childTransportJetCLM k z=ᵐ[ballMeasure] (fun x => WithLp.toLp 2 (Fin.cases
      (f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) 0)
      (fun j => sourceScale⁻¹*f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) (childAxis j).succ))) := by
  have hi (i : Fin 4) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (childTransportComponentCLM_ae_of_ae k z f he i))
  filter_upwards [physicalFourJetCLM_ae (fun i => childTransportComponentCLM k i z),ae_all_iff.mpr hi] with x hx hi
  change physicalFourJetCLM (fun i => childTransportComponentCLM k i z) x=_
  rw [hx]
  ext i
  exact hi i

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralLocalAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : Fin 3 → ℝ} (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)

lemma centralFullJetCLM_smooth_ae (f : centralSmoothFunctions) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
      centralFullJetCLM s (centralEmbedL s f) x=
        piSmoothJet (fun y => f (sourcePairCoordinates y)) (WithLp.ofLp x) := by
  have hi (i : Fin 4) := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
      (centralPhysicalWholeCLM_smooth_ae f i))
  filter_upwards [physicalFourJetCLM_ae (fun i => centralPhysicalWholeCLM (centralSmoothJet f i)),
    ae_all_iff.mpr hi] with x hx hi
  intro hy
  simp only [Function.comp_apply] at hi
  change physicalFourJetCLM (fun i => centralPhysicalWholeCLM (centralSmoothJet f i)) x=_
  rw [hx]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [indicator_of_mem hy,piSmoothJet,PiLp.toLp_apply,Fin.cases_zero,
      centralJetField,Matrix.cons_val_zero] using hi 0
  · change centralPhysicalWholeCLM (centralSmoothJet f j.succ) (WithLp.ofLp x)=_
    rw [hi j.succ,indicator_of_mem hy,central_parent_partial]
    rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralJetIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

lemma H1_add_jet_ae (u v : H1) :
    (u+v).val=ᵐ[ballMeasure] (fun x => u.val x+v.val x) := by
  exact Lp.coeFn_add u.val v.val

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CentralCylinderGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma flatCylinderMatrix_symmetric (s : Fin 3 → ℝ) :
    (flatCylinderMatrix s)ᵀ=flatCylinderMatrix s := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AttachedFlatTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma attachedFlatTensor_symmetric (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (x : Fin 3 → ℝ) : (attachedFlatTensor s a i j x)ᵀ=attachedFlatTensor s a i j x := by
  simp only [attachedFlatTensor,Matrix.transpose_smul,Matrix.transpose_mul,
    Matrix.transpose_transpose,flatCylinderMatrix_symmetric,Matrix.mul_assoc]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AttachedFlatTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma attachedPhysicalFlatTensor_symmetric (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (y : Fin 3 → ℝ) :
    (attachedPhysicalFlatTensor s a i j y)ᵀ=attachedPhysicalFlatTensor s a i j y :=
  attachedFlatTensor_symmetric s a i j _

theorem attachedPhysicalFlatTensor_elliptic (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a : ℝ} (ha : a≠0) (i j : Fin 4) :
    ∃ c C : ℝ,0 < c ∧ c<C ∧
      ∀ y∈sourceCollarPiece i j '' sourceExtendedBox (-(1:ℝ)/100) (1/100),
        ∀ v : Fin 3 → ℝ,c*‖v‖^2≤v ⬝ᵥ (attachedPhysicalFlatTensor s a i j y*ᵥv) ∧
          v ⬝ᵥ (attachedPhysicalFlatTensor s a i j y*ᵥv)≤C*‖v‖^2 := by
  obtain ⟨c,C,hc,hcC,h⟩ := attachedFlatTensor_elliptic s hs ha i j
  refine ⟨c,C,hc,hcC,?_⟩
  rintro _ ⟨x,hx,rfl⟩ v
  simpa only [attachedPhysicalFlatTensor,
    sourceCollarInverse_extended i j (le_refl _) (le_refl _) hx] using h x hx v

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

lemma RegularPatch.mono {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {O W : Set Coord3} (h : RegularPatch u A O) (hW : IsOpen W) (hWO : W ⊆ O) :
    RegularPatch u A W :=
  ⟨hW,h.2.1.mono hWO,h.2.2.1.mono hWO,h.2.2.2.mono hWO⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalTensorPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise
attribute [local instance] OAI.ScalarConductivity.physicalTensorPatchMeasurableSpace
local instance physicalTensorPatchBorelSpace : BorelSpace (Matrix (Fin 3) (Fin 3) ℝ) := ⟨rfl⟩

lemma continuousAt_sourceCollarInverse_patch (i j : Fin 4) {y : Fin 3 → ℝ}
    (hy : y∈sourceFlatPatch i j) : ContinuousAt (sourceCollarInverse i j) y := by
  obtain ⟨x,hx,rfl⟩ := hy
  obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp hx
  have hr : 0 < sourceCollarRadius j (x 0) (x 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended j ht hj).1
  have hrad := sourceCollarPiece_radial_pos i j hr.le hi
  have htime := sourceCollarPiece_time_pos i j hr.le (by linarith [ht.2] : x 0≤1) hi hj
  have hc : Continuous sourceCollarTime := by
    unfold sourceCollarTime sourceCrossCoordinates sourceRadial
    fun_prop
  have hcR : Continuous sourceRadial := by unfold sourceRadial; fun_prop
  have hcX : Continuous sourceCrossCoordinates := by
    unfold sourceCrossCoordinates sourceRadial
    fun_prop
  unfold sourceCollarInverse
  apply continuousAt_pi.mpr
  intro k
  fin_cases k
  · exact hc.continuousAt
  · apply ContinuousAt.div
    · unfold squareFaceParameter
      fun_prop
    · exact hcR.continuousAt
    · rw [hrad]
      exact hr.ne'
  · apply ContinuousAt.div
    · exact ((show Continuous (squareFaceParameter j) by
        unfold squareFaceParameter; fun_prop).comp hcX).continuousAt
    · exact continuousAt_const.sub hc.continuousAt
    · rw [htime]
      linarith [ht.2]

lemma continuousOn_attachedPhysicalFlatTensor (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) : ContinuousOn (attachedPhysicalFlatTensor s a i j) (sourceFlatPatch i j) := by
  apply (continuousOn_attachedFlatTensor s ha i j).comp
    (fun y hy => (continuousAt_sourceCollarInverse_patch i j hy).continuousWithinAt)
  rintro _ ⟨x,hx,rfl⟩
  simpa only [sourceCollarInverse_extended i j (le_refl _) (le_refl _) hx] using hx

lemma measurable_attachedPatchTensor (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) : Measurable (attachedPatchTensor s a i j) := by
  classical
  exact (continuousOn_attachedPhysicalFlatTensor s ha i j).measurable_piecewise
    continuousOn_const (isCompact_sourceFlatPatch i j).isClosed.measurableSet

lemma attachedPatchTensor_symmetric (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (y : Fin 3 → ℝ) : (attachedPatchTensor s a i j y)ᵀ=attachedPatchTensor s a i j y := by
  classical
  unfold attachedPatchTensor
  split_ifs
  · exact attachedPhysicalFlatTensor_symmetric s a i j y
  · exact Matrix.transpose_one

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma attachedFaceTensorList_cons (s : Fin 3 → ℝ) (a : ℝ)
    (k : Fin 4 × Fin 4) (ks : List (Fin 4 × Fin 4)) (y : Fin 3 → ℝ) :
    attachedFaceTensorList s a (k::ks) y=
      (by classical exact if y∈sourceFlatPatch k.1 k.2 then attachedPatchTensor s a k.1 k.2 y
        else attachedFaceTensorList s a ks y) := by
  classical
  rfl

attribute [local instance] OAI.ScalarConductivity.attachedFaceTensorListMeasurableSpace
local instance attachedFaceTensorListBorelSpace_r97ec74_1 : BorelSpace (Matrix (Fin 3) (Fin 3) ℝ) := ⟨rfl⟩
lemma attachedFaceTensorList_measurable (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    (ks : List (Fin 4 × Fin 4)) : Measurable (attachedFaceTensorList s a ks) := by
  classical
  induction ks with
  | nil => exact measurable_const
  | cons k ks ih =>
    exact Measurable.ite (isCompact_sourceFlatPatch k.1 k.2).isClosed.measurableSet
      (measurable_attachedPatchTensor s ha k.1 k.2) ih

lemma attachedFaceTensorList_symmetric (s : Fin 3 → ℝ) (a : ℝ)
    (ks : List (Fin 4 × Fin 4)) (y : Fin 3 → ℝ) :
    (attachedFaceTensorList s a ks y)ᵀ=attachedFaceTensorList s a ks y := by
  classical
  induction ks with
  | nil => exact Matrix.transpose_one
  | cons k ks ih =>
    simp only [attachedFaceTensorList_cons]
    split_ifs
    · exact attachedPatchTensor_symmetric s a k.1 k.2 y
    · exact ih

lemma attachedFaceTensorList_elliptic (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a : ℝ} (ha : a≠0) (ks : List (Fin 4 × Fin 4)) :
    ∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
      c*‖v‖^2≤v ⬝ᵥ (attachedFaceTensorList s a ks y*ᵥv) ∧
        v ⬝ᵥ (attachedFaceTensorList s a ks y*ᵥv)≤C*‖v‖^2 := by
  classical
  induction ks with
  | nil =>
    obtain ⟨c,C,hc,hcC,h⟩ := identity_matrix_energy_bounds
    exact ⟨c,C,hc,hcC,fun _ => h⟩
  | cons k ks ih =>
    obtain ⟨c,C,hc,hcC,h⟩ := ih
    obtain ⟨d,D,hd,hdD,hk⟩ := attachedPhysicalFlatTensor_elliptic s hs ha k.1 k.2
    refine ⟨min c d,max C D,lt_min hc hd,
      lt_of_le_of_lt (min_le_left _ _) (hcC.trans_le (le_max_left _ _)),?_⟩
    intro y v
    simp only [attachedFaceTensorList_cons]
    by_cases hy : y∈sourceFlatPatch k.1 k.2
    · simp only [ite_eq_left hy,attachedPatchTensor]
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
          (hk y hy v).1,
        (hk y hy v).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))⟩
    · simp only [ite_eq_right hy]
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
          (h y v).1,
        (h y v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩

lemma attachedFaceTensorList_outside (s : Fin 3 → ℝ) (a : ℝ)
    (ks : List (Fin 4 × Fin 4)) (y : Fin 3 → ℝ)
    (hy : ∀ k∈ks,y∉sourceFlatPatch k.1 k.2) : attachedFaceTensorList s a ks y=1 := by
  classical
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simpa only [attachedFaceTensorList,List.foldr_cons,ite_eq_right (hy k (List.mem_cons_self))]
      using ih (fun l hl => hy l (List.mem_cons_of_mem k hl))

lemma attachedFaceTensorList_local (s : Fin 3 → ℝ) (a : ℝ)
    (ks : List (Fin 4 × Fin 4)) (y : Fin 3 → ℝ)
    (hy : ∃ k∈ks,y∈sourceFlatPatch k.1 k.2) :
    ∃ k∈ks,y∈sourceFlatPatch k.1 k.2 ∧
      attachedFaceTensorList s a ks y=attachedPhysicalFlatTensor s a k.1 k.2 y := by
  classical
  induction ks with
  | nil => simp at hy
  | cons k ks ih =>
    by_cases hk : y∈sourceFlatPatch k.1 k.2
    · refine ⟨k,List.mem_cons_self,hk,?_⟩
      simp only [attachedFaceTensorList,List.foldr_cons,ite_eq_left hk,attachedPatchTensor]
    · obtain ⟨l,hl,hy⟩ := hy
      obtain ⟨l,hl,hly,he⟩ := ih ⟨l,(List.mem_cons.mp hl).resolve_left
        (fun e => hk (e ▸ hy)),hy⟩
      refine ⟨l,List.mem_cons_of_mem k hl,hly,?_⟩
      simpa only [attachedFaceTensorList,List.foldr_cons,ite_eq_right hk] using he

theorem attachedCollarTensor_properties (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a : ℝ} (ha : a≠0) :
    Measurable (attachedCollarTensor s a) ∧
      (∀ y,(attachedCollarTensor s a y)ᵀ=attachedCollarTensor s a y) ∧
      (∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
        c*‖v‖^2≤v ⬝ᵥ (attachedCollarTensor s a y*ᵥv) ∧
          v ⬝ᵥ (attachedCollarTensor s a y*ᵥv)≤C*‖v‖^2) ∧
      (∀ y,(∀ i j,y∉sourceFlatPatch i j) → attachedCollarTensor s a y=1) ∧
      (∀ y,(∃ i j,y∈sourceFlatPatch i j) → ∃ i j,y∈sourceFlatPatch i j ∧
        attachedCollarTensor s a y=attachedPhysicalFlatTensor s a i j y) := by
  refine ⟨attachedFaceTensorList_measurable s ha _,
    attachedFaceTensorList_symmetric s a _,attachedFaceTensorList_elliptic s hs ha _,?_,?_⟩
  · intro y hy
    exact attachedFaceTensorList_outside s a _ y (fun k _ => hy k.1 k.2)
  · rintro y ⟨i,j,hy⟩
    obtain ⟨k,_,hk,he⟩ := attachedFaceTensorList_local s a
      (Finset.univ : Finset (Fin 4 × Fin 4)).toList y ⟨(i,j),by simp,hy⟩
    exact ⟨k.1,k.2,hk,he⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalTensorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma attachedFaceTensorList_bounded (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    (ks : List (Fin 4 × Fin 4)) :
    ∃ B : ℝ,0<B ∧ ∀ y,‖attachedFaceTensorList s a ks y‖≤B := by
  classical
  induction ks with
  | nil =>
    exact ⟨‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖+1,by positivity,fun _ => by
      change ‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖≤_; linarith⟩
  | cons k ks ih =>
    obtain ⟨B,hB,h⟩ := ih
    obtain ⟨C,hC⟩ := (isCompact_sourceFlatPatch k.1 k.2).exists_bound_of_continuousOn
      (continuousOn_attachedPhysicalFlatTensor s ha k.1 k.2)
    refine ⟨max B C,lt_of_lt_of_le hB (le_max_left _ _),?_⟩
    intro y
    rw [attachedFaceTensorList_cons]
    by_cases hy : y∈sourceFlatPatch k.1 k.2
    · simp only [ite_eq_left hy,attachedPatchTensor]
      exact (hC y hy).trans (le_max_right _ _)
    · simp only [ite_eq_right hy]
      exact (h y).trans (le_max_left _ _)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ParentEndPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma exists_nonneg_band_cutoff {l₀ l r r₀ : ℝ} (hl : l₀<l) (hr : r < r₀)
    (hl₀ : -(1:ℝ)/100≤l₀) (hr₀ : r₀≤1/100) :
    ∃ χ : (Fin 3 → ℝ) → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) χ ∧ HasCompactSupport χ ∧
      (∀ x,χ x∈Icc 0 1) ∧ tsupport χ⊆sourceClosedCollarBand l₀ r₀ ∧
      (∀ x∈sourceClosedCollarBand l r,χ=ᶠ[𝓝 x] (fun _ => 1)) := by
  have hbig := isCompact_sourceClosedCollarBand hl₀ hr₀
  have hsmall := isCompact_sourceClosedCollarBand (hl₀.trans hl.le) (hr.le.trans hr₀)
  have hi : sourceClosedCollarBand l r⊆interior (sourceClosedCollarBand l₀ r₀) := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    have hm := locallyLipschitz_sourceCollarTime.continuous.continuousAt
      (isOpen_Ioo.mem_nhds (show sourceCollarTime x∈Ioo l₀ r₀ from
        ⟨hl.trans_le hx.1,hx.2.trans_lt hr⟩))
    exact mem_of_superset hm (fun y hy => ⟨hy.1.le,hy.2.le⟩)
  obtain ⟨χ,hχ1,hχ0,hχb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Fin 3 → ℝ)) hsmall.isClosed hi (n:=↑(⊤:ℕ∞))
  refine ⟨χ,χ.contMDiff.contDiff,HasCompactSupport.intro hbig hχ0,hχb,?_,?_⟩
  · apply closure_minimal _ hbig.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  · intro x hx
    exact hχ1.filter_mono (nhds_le_nhdsSet hx)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CentralSeamCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceJoinInner_bounds {y : Fin 3 → ℝ}
    (hy : -2*centralThickness ≤ sourceCollarTime y) :
    |y 0|≤1604/1000 ∧ |y 1|≤1002/1000 ∧ |y 2|≤1004/1000 := by
  have hh := (sourceCollarTime_ge_iff y (-2*centralThickness)).mp hy
  have hx := (le_max_left (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  have hy' := (le_max_right (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  norm_num [centralThickness,sourceRadialWidth,sourceHole,sourceLength] at hx hy' hh ⊢
  exact ⟨by linarith,by linarith,by linarith [hh.1]⟩

lemma sourceJoinChild_far_parent (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : -2*centralThickness ≤ sourceCollarTime y) :
    2*centralThickness ≤ sourceCollarTime (sourceChildCoordinates (actualChildSign k) y) := by
  obtain ⟨h₀,h₁,h₂⟩ := sourceJoinInner_bounds hy
  have hsign : |actualChildSign k|=1 := by fin_cases k <;> norm_num [actualChildSign]
  have ha : |actualChildSign k*sourceOffset|=sourceOffset := by
    rw [abs_mul,hsign,one_mul]; norm_num [sourceOffset]
  have hu := abs_add_le (sourceScale*y 1) (actualChildSign k*sourceOffset)
  rw [abs_mul,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale]),ha] at hu
  have hl := abs_add_le (-sourceScale*y 1) (sourceScale*y 1+actualChildSign k*sourceOffset)
  have he : -sourceScale*y 1+(sourceScale*y 1+actualChildSign k*sourceOffset)=
    actualChildSign k*sourceOffset := by ring
  rw [he,ha,abs_mul,abs_neg,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])] at hl
  apply (sourceCollarTime_ge_iff _ _).mpr
  change |sourceScale*y 2|≤_ ∧ _≤ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
    (|sourceScale*y 0|) ∧ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
      (|sourceScale*y 0|)≤_
  simp only [abs_mul,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])]
  constructor
  · norm_num [sourceScale,centralThickness]; linarith
  · constructor
    · apply le_trans _ (le_max_left _ _)
      norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
      linarith
    · apply max_le
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ChildFullEndH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma childH10Transport_local_jet (k : Fin 2) (u : H10)
    {D : Set (Fin 3 → ℝ)}
    (hD : ∀ y∈D,WithLp.toLp 2 y∈ball)
    (V : (Fin 3 → ℝ) → ℝ) (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (he : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D →
      weakValue u.val x=V (WithLp.ofLp x) ∧
      ∀ i,weakGradient u.val x i=G (WithLp.ofLp x) i) :
    ∀ᵐ x∂ballMeasure,
      (sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)∈D →
      weakValue (childH10Transport k u) x=
        V ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) ∧
      ∀ i,weakGradient (childH10Transport k u) x i=
        sourceScale⁻¹*G ((sourceChildHomeomorph (actualChildSign k)).symm
          (WithLp.ofLp x)) (childAxis i) := by
  classical
  let f : (Fin 3 → ℝ) → JetFiber := fun y =>
    if WithLp.toLp 2 y∈ball then u.val.val (WithLp.toLp 2 y) else 0
  have hj := childTransportJetCLM_ae_of_ae k u.val.val f
    (ballWholePiJetCLM_ae_of_ae u.val.val
      (fun y => u.val.val (WithLp.toLp 2 y)) (by filter_upwards [] with x; rfl))
  have he₀ := (ae_restrict_iff' (show MeasurableSet ball from
    Metric.isOpen_ball.measurableSet)).mp he
  have he₁ := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae he₀
  have he₂ := (sourceChildInverse_quasi (actualChildSign k)).ae he₁
  have he₃ := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae he₂)
  filter_upwards [hj,he₃] with x hj hx hm
  have hb := hD _ hm
  have hloc := hx hb hm
  constructor
  · change (childTransportJetCLM k u.val.val x) 0=_
    rw [hj]
    change (f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))) 0=_
    rw [show f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))=
      u.val.val (WithLp.toLp 2 ((sourceChildHomeomorph (actualChildSign k)).symm
        (WithLp.ofLp x))) from ite_eq_left hb]
    exact hloc.1
  · intro i
    change (childTransportJetCLM k u.val.val x) i.succ=_
    rw [hj]
    change sourceScale⁻¹*(f ((sourceChildHomeomorph (actualChildSign k)).symm
      (WithLp.ofLp x))) (childAxis i).succ=_
    rw [show f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))=
      u.val.val (WithLp.toLp 2 ((sourceChildHomeomorph (actualChildSign k)).symm
        (WithLp.ofLp x))) from ite_eq_left hb]
    exact congrArg (fun q : ℝ => sourceScale⁻¹*q) (hloc.2 (childAxis i))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalChildAttachedCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma childH10Transport_zero_on (k : Fin 2) (u : H10) (D : Set (Fin 3 → ℝ))
    (he : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D →
      weakValue u.val x=0 ∧ ∀ i,weakGradient u.val x i=0) :
    ∀ᵐ x∂ballMeasure,
      (sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)∈D →
      weakValue (childH10Transport k u) x=0 ∧
      ∀ i,weakGradient (childH10Transport k u) x i=0 := by
  classical
  let f : (Fin 3 → ℝ) → JetFiber := fun y =>
    if WithLp.toLp 2 y∈ball then u.val.val (WithLp.toLp 2 y) else 0
  have hj := childTransportJetCLM_ae_of_ae k u.val.val f
    (ballWholePiJetCLM_ae_of_ae u.val.val
      (fun y => u.val.val (WithLp.toLp 2 y)) (by filter_upwards [] with x; rfl))
  have he₀ := (ae_restrict_iff' (show MeasurableSet ball from
    Metric.isOpen_ball.measurableSet)).mp he
  have he₁ := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae he₀
  have he₂ := (sourceChildInverse_quasi (actualChildSign k)).ae he₁
  have he₃ := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae he₂)
  filter_upwards [hj,he₃] with x hj hx hm
  have hf : f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))=0 := by
    dsimp only [f]
    split_ifs with hb
    · have hh := hx hb hm
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hh.1
      · exact hh.2 j
    · rfl
  constructor
  · change (childTransportJetCLM k u.val.val x) 0=0
    rw [hj]
    change (f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))) 0=0
    rw [hf]
    rfl
  · intro i
    change (childTransportJetCLM k u.val.val x) i.succ=0
    rw [hj]
    change sourceScale⁻¹*(f ((sourceChildHomeomorph (actualChildSign k)).symm
      (WithLp.ofLp x))) (childAxis i).succ=0
    rw [hf]
    simp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalAttachedAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma weak_jet_eq_iff (u : H1) (x : R3) (v : ℝ) (g : Fin 3 → ℝ) :
    u.val x=physicalJet v g ↔ weakValue u x=v ∧ ∀ i,weakGradient u x i=g i := by
  constructor
  · intro h
    constructor
    · exact congrArg (fun z : JetFiber => z 0) h
    · intro i
      exact congrArg (fun z : JetFiber => z i.succ) h
  · rintro ⟨hv,hg⟩
    ext i
    exact Fin.cases hv hg i

lemma weak_jet_zero_iff (u : H1) (x : R3) :
    u.val x=0 ↔ weakValue u x=0 ∧ ∀ i,weakGradient u x i=0 := by
  have he : physicalJet 0 (fun _ => 0)=0 := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  rw [←he,weak_jet_eq_iff]

lemma H1JetOn.mono {u : H1} {D E : Set (Fin 3 → ℝ)} {f : R3 → JetFiber}
    (h : H1JetOn u D f) (hED : E⊆D) : H1JetOn u E f := by
  filter_upwards [h] with x hx hy
  exact hx (hED hy)

lemma H1JetOn.add {u v : H1} {D : Set (Fin 3 → ℝ)} {f g : R3 → JetFiber}
    (hu : H1JetOn u D f) (hv : H1JetOn v D g) :
    H1JetOn (u+v) D (fun x => f x+g x) := by
  filter_upwards [hu,hv,H1_add_jet_ae u v] with x hx hy he hm
  rw [he,hx hm,hy hm]

lemma H1JetOn.add_zero {u v : H1} {D : Set (Fin 3 → ℝ)} {f : R3 → JetFiber}
    (hu : H1JetOn u D f) (hv : H1JetOn v D (fun _ => 0)) : H1JetOn (u+v) D f := by
  simpa only [_root_.add_zero] using hu.add hv

lemma H1JetOn.zero_add {u v : H1} {D : Set (Fin 3 → ℝ)} {f : R3 → JetFiber}
    (hu : H1JetOn u D (fun _ => 0)) (hv : H1JetOn v D f) : H1JetOn (u+v) D f := by
  simpa only [_root_.zero_add] using hu.add hv

lemma H1JetOn.of_weak {u : H1} {D : Set (Fin 3 → ℝ)} {v : R3 → ℝ}
    {g : R3 → Fin 3 → ℝ}
    (h : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → weakValue u x=v x ∧
      ∀ i,weakGradient u x i=g x i) : H1JetOn u D (fun x => physicalJet (v x) (g x)) := by
  filter_upwards [h] with x hx hm
  exact (weak_jet_eq_iff u x _ _).mpr (hx hm)

lemma H1JetOn.zero_of_weak {u : H1} {D : Set (Fin 3 → ℝ)}
    (h : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → weakValue u x=0 ∧
      ∀ i,weakGradient u x i=0) : H1JetOn u D (fun _ => 0) := by
  filter_upwards [h] with x hx hm
  exact (weak_jet_zero_iff u x).mpr (hx hm)

end ScalarConductivity
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusSmoothModeJet
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal

lemma torusAngles_shift (n : Fin 2 → ℤ) (x : Coord3) :
    torusAngles (x+angularShift (2*Real.pi) n)=torusAngles x := by
  have hπ : 2*Real.pi≠0 := by positivity
  ext i
  fin_cases i <;> simp [torusAngles,angularShift,add_div,hπ,mul_div_cancel_left₀]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusAffineField
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

lemma torusAffineField_smooth {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (κ : ℝ) (f : TorusL2) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (torusAffineField s κ f) {x | 0<x 0} :=
  (show ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => κ*x 0) by fun_prop).contDiffOn.add
    (torusRealContinuation_smooth hs f)

lemma torusAffineField_periodic (s : Fin 3 → ℝ) (κ : ℝ) (f : TorusL2) :
    AngularPeriodic (2*Real.pi) (torusAffineField s κ f) := by
  intro n x
  simp only [torusAffineField,torusRealContinuation,torusAngles_shift]
  simp [angularShift]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FieldVectorCLM
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
open scoped Matrix.Norms.Elementwise ENNReal

lemma regularRegion_differentiable {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U : Set Coord3} {x : Coord3} (hx : x ∈ regularRegion u A U) : DifferentiableAt ℝ u x := by
  obtain ⟨V,hVU,hV,hxV⟩ := mem_regularRegion_iff.mp hx
  exact (hV.2.1.differentiableOn (by simp) x hxV).differentiableAt (hV.1.mem_nhds hxV)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_C1VoltageApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped ENNReal Convolution

lemma coordDyadicBump_radius : Tendsto (fun n => (coordDyadicBump n).rOut) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [MeasurableSpace F] [BorelSpace F] in
lemma coordMollify_bound (φ : CoordBump) {f : Coord3 → F} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x,‖f x‖≤M) (x : Coord3) : ‖coordMollify φ f x‖≤M := by
  have hM0 : 0≤M := (norm_nonneg (f 0)).trans (hM 0)
  have h := dist_convolution_le (μ := volume) (z₀ := (0:F)) hM0 φ.support_normed_eq.subset
    φ.nonneg_normed φ.integral_normed hf.aestronglyMeasurable
    (fun y (_ : y∈Metric.ball x φ.rOut) => by simpa using hM y)
  simpa only [coordMollify,dist_zero_right] using h

lemma coordMollify_toLp_tendsto {f : Coord3 → F} (hf : Continuous f)
    (hfc : HasCompactSupport f) {U : Set Coord3}
    (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U) :
    Tendsto (fun n => (coordMollify_memLp (coordDyadicBump n) hf hUb hUm).toLp _)
      atTop (𝓝 ((continuous_memLp_bounded_coord hf hUb hUm).toLp _)) := by
  let : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUb.measure_lt_top.ne
  obtain ⟨M,hM⟩ := hfc.exists_bound_of_continuous hf
  have hM0 : 0≤M := (norm_nonneg (f 0)).trans (hM 0)
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => (coordMollify_smooth (coordDyadicBump n) hf).continuous.aestronglyMeasurable)
    (continuous_memLp_bounded_coord hf hUb hUm)
  · apply unifIntegrable_of_norm_domination
      (unifIntegrable_const (by norm_num : (1:ℝ≥0∞)≤2) (by norm_num)
        (memLp_const M))
      (fun index =>
        (coordMollify_smooth (coordDyadicBump index) hf).continuous.aestronglyMeasurable)
    intro n
    exact ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg hM0] using
        coordMollify_bound (coordDyadicBump n) hf hM x)
  · exact ae_of_all _ (fun x => ContDiffBump.convolution_tendsto_right_of_continuous
      coordDyadicBump_radius hf x)

omit [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
lemma coordMollify_fderiv {g : Coord3 → F} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (φ : CoordBump) :
    fderiv ℝ (coordMollify φ g)=coordMollify φ (fderiv ℝ g) := by
  funext x
  have h := (hgc.hasFDerivAt_convolution_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.integrable_normed.locallyIntegrable hg x).fderiv
  exact h

theorem compact_C1_voltageJet_mem {g : Coord3 → Fin 2 → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) {U : Set Coord3}
    (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U) :
    ∃ (hv : MemLp g 2 (volume.restrict U))
      (hd : MemLp (voltageGradient g) 2 (volume.restrict U)),
      (hv.toLp _,hd.toLp _)∈voltageH1Jets volume U := by
  have hv := continuous_memLp_bounded_coord hg.continuous hUb hUm
  have hD := continuous_memLp_bounded_coord (hg.continuous_fderiv (by norm_num)) hUb hUm
  have hd : MemLp (voltageGradient g) 2 (volume.restrict U) :=
    gradientVectorCLM.comp_memLp' hD
  let gn (n : ℕ) := coordMollify (coordDyadicBump n) g
  have hgn (n : ℕ) : ContDiff ℝ (↑(⊤:ℕ∞)) (gn n) := coordMollify_smooth _ hg.continuous
  have hgv (n : ℕ) := coordMollify_memLp (coordDyadicBump n) hg.continuous hUb hUm
  have hgD (n : ℕ) : MemLp (fderiv ℝ (gn n)) 2 (volume.restrict U) := by
    rw [show fderiv ℝ (gn n)=coordMollify (coordDyadicBump n) (fderiv ℝ g) from
      coordMollify_fderiv hg hgc _]
    exact coordMollify_memLp _ (hg.continuous_fderiv (by norm_num)) hUb hUm
  have hgd (n : ℕ) : MemLp (voltageGradient (gn n)) 2 (volume.restrict U) :=
    gradientVectorCLM.comp_memLp' (hgD n)
  have he (f : Coord3 → Fin 2 → ℝ)
      (hdf : MemLp (fderiv ℝ f) 2 (volume.restrict U))
      (hgf : MemLp (voltageGradient f) 2 (volume.restrict U)) :
      gradientVectorCLM.compLpL 2 (volume.restrict U) (hdf.toLp _)=hgf.toLp _ := by
    apply Lp.ext
    filter_upwards [gradientVectorCLM.coeFn_compLp (hdf.toLp _),hdf.coeFn_toLp,hgf.coeFn_toLp]
      with x hx hy hz
    change (gradientVectorCLM.compLp (hdf.toLp _)) x = _
    rw [hx,hy,hz]
    rfl
  have hDt : Tendsto (fun n => (hgD n).toLp _) atTop (𝓝 (hD.toLp _)) := by
    convert coordMollify_toLp_tendsto (hg.continuous_fderiv (by norm_num))
      (hgc.fderiv ℝ) hUb hUm using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    filter_upwards [(hgD n).coeFn_toLp,
      (coordMollify_memLp (coordDyadicBump n) (hg.continuous_fderiv (by norm_num)) hUb hUm).coeFn_toLp]
      with x hx hy
    rw [hx,hy,coordMollify_fderiv hg hgc]
  have hdt : Tendsto (fun n => (hgd n).toLp _) atTop (𝓝 (hd.toLp _)) := by
    have hh := (gradientVectorCLM.compLpL 2 (volume.restrict U)).continuous.tendsto (hD.toLp _) |>.comp hDt
    rw [he g hD hd] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact (he (gn n) (hgD n) (hgd n)).symm
  refine ⟨hv,hd,?_⟩
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    ((coordMollify_toLp_tendsto hg.continuous hgc hUb hUm).prodMk_nhds hdt)
  exact Eventually.of_forall (fun n => (Submodule.span ℝ (smoothVoltageJets volume U)).le_topologicalClosure
    (Submodule.subset_span ⟨gn n,hgn n,hgv n,hgd n,rfl⟩))

theorem C1_voltageJet_mem {v : Coord3 → Fin 2 → ℝ} (hv : ContDiff ℝ 1 v)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U) :
    ∃ (hu : MemLp v 2 (volume.restrict U))
      (hd : MemLp (voltageGradient v) 2 (volume.restrict U)),
      (hu.toLp _,hd.toLp _)∈voltageH1Jets volume U := by
  obtain ⟨R,hR⟩ := hUb.exists_norm_le
  let φ : CoordBump := {
    rIn := max R 0+1
    rOut := max R 0+2
    rIn_pos := by have := le_max_right R 0; linarith
    rIn_lt_rOut := by linarith }
  let g : Coord3 → Fin 2 → ℝ := fun x => φ x • v x
  have hg : ContDiff ℝ 1 g := φ.contDiff.smul hv
  have hgc : HasCompactSupport g := φ.hasCompactSupport.smul_right
  have heq (x : Coord3) (hx : x∈U) : g =ᶠ[𝓝 x] v := by
    have hxball : x∈Metric.ball (0:Coord3) φ.rIn := by
      rw [Metric.mem_ball,dist_zero_right]
      have := hR x hx
      have := le_max_left R 0
      dsimp [φ]
      linarith
    filter_upwards [φ.eventuallyEq_one_of_mem_ball hxball] with y hy
    dsimp [g]
    rw [hy]
    exact one_smul ℝ (v y)
  have hu := continuous_memLp_bounded_coord hv.continuous hUb hUm
  have hd : MemLp (voltageGradient v) 2 (volume.restrict U) :=
    gradientVectorCLM.comp_memLp'
      (continuous_memLp_bounded_coord (hv.continuous_fderiv (by norm_num)) hUb hUm)
  obtain ⟨hgu,hgd,hmem⟩ := compact_C1_voltageJet_mem hg hgc hUb hUm
  have huEq : hgu.toLp g=hu.toLp v := by
    apply Lp.ext
    filter_upwards [hgu.coeFn_toLp,hu.coeFn_toLp,ae_restrict_mem hUm] with x hx hy hz
    rw [hx,hy]
    exact (heq x hz).eq_of_nhds
  have hdEq : hgd.toLp (voltageGradient g)=hd.toLp (voltageGradient v) := by
    apply Lp.ext
    filter_upwards [hgd.coeFn_toLp,hd.coeFn_toLp,ae_restrict_mem hUm] with x hx hy hz
    rw [hx,hy]
    exact congrArg (fun D => fieldVector (gradientColumns D)) (heq x hz).fderiv_eq
  exact ⟨hu,hd,by rwa [huEq,hdEq] at hmem⟩

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

lemma axialZeroExtension_contDiff {n : WithTop ℕ∞} {d e : ℝ} (he : 0<e)
    {f : Coord3 → E} (hf : ContDiffOn ℝ n f {x | d<x 0})
    (hz : ∀ x,x 0∈Icc d (d+e) → f x=0) : ContDiff ℝ n (axialZeroExtension d e f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x 0<d+e
  · exact contDiffAt_const.congr_of_eventuallyEq (axialZeroExtension_eventually_zero he hz hx)
  · have hx' : d+e/2<x 0 := by linarith
    exact (hf.contDiffAt ((axial_halfspace_open d).mem_nhds (show d<x 0 by linarith))).congr_of_eventuallyEq
      (axialZeroExtension_eventually_self hx')

omit [NormedSpace ℝ E] in
lemma axialZeroExtension_periodic {T d e : ℝ} {f : Coord3 → E}
    (hf : AngularPeriodic T f) : AngularPeriodic T (axialZeroExtension d e f) := by
  intro n x
  change (if d+e/2<x 0+0 then f (x+angularShift T n) else 0)=_
  rw [add_zero,hf n x]
  rfl

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

lemma torusEndingCorrection_C2 {d e : ℝ} (he : 0<e) {v f : Coord3 → ℝ}
    (hv : ContDiff ℝ 2 v) (hf : ContDiffOn ℝ 2 f {x | d<x 0})
    (hz : ∀ x,x 0∈Ioo d (d+e) → v x=f x) :
    ContDiff ℝ 2 (torusEndingCorrection d e v f) := by
  apply axialZeroExtension_contDiff (by linarith : 0<e/2)
  · exact (hv.contDiffOn.sub hf).mono (fun x hx => by dsimp at hx ⊢; linarith)
  · intro x hx
    change v x-f x=0
    exact sub_eq_zero.mpr (hz x ⟨by linarith [hx.1],by linarith [hx.2]⟩)

lemma torusEndingCorrection_periodic {T d e : ℝ} {v f : Coord3 → ℝ}
    (hv : AngularPeriodic T v) (hf : AngularPeriodic T f) :
    AngularPeriodic T (torusEndingCorrection d e v f) := by
  apply axialZeroExtension_periodic
  intro n x
  change v (x+angularShift T n)-f (x+angularShift T n)=v x-f x
  rw [hv n x,hf n x]

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
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FiniteEndPhysicalDescent
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

lemma sourceRealFlat_angles (y : Coord3) :
    torusAngles (sourceRealFlat y)=sourcePhysicalAngles y := by
  ext i
  fin_cases i <;> rfl

lemma physicalPeriodicField_local_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) {x y : Coord3}
    (hx : ∀ i,sourceComplexDirections x i≠0) (hy : ∀ i,sourceComplexDirections y i≠0) :
    physicalPeriodicField f y=f (sourceLocalFlat x y) := by
  unfold physicalPeriodicField
  apply hp.eq_of_angles (show sourceRealFlat y 0=sourceLocalFlat x y 0 from rfl)
  exact (sourceRealFlat_angles y).trans (sourceLocalFlat_angles hx hy).symm

theorem physicalPeriodicField_localLip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) (hf : ContDiff ℝ 1 f)
    {x : Coord3} (hx : ∀ i,sourceComplexDirections x i≠0) :
    LocalLipAt (physicalPeriodicField f) x := by
  apply ((localLipAt_of_contDiffAt hf.contDiffAt).comp
    (sourceLocalFlat_localLip hx)).congr
  have hd : ∀ᶠ y in 𝓝 x,∀ i,sourceComplexDirections y i≠0 := by
    rw [eventually_all]
    intro i
    exact (locallyLipschitz_sourceDirection i).continuous.continuousAt
      (isOpen_ne.mem_nhds (hx i))
  filter_upwards [hd] with y hy
  exact (physicalPeriodicField_local_eq hp hx hy).symm

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


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i f))

lemma branchFinitePair_periodic_v : AngularPeriodic (2*Real.pi) (branchFinitePair i z).v := by
  intro n x
  simp only [branchFinitePair_v,z.periodic_v n x]

lemma branchCorrection_C2
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) : ContDiff ℝ 2 (branchCorrection i z j) := by
  exact torusEndingCorrection_C2 z.e_pos (contDiff_pi.mp (branchFinitePair i z).smooth j)
    (((torusAffineField_smooth hs _ _).of_le
      (show (2 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono
        (fun x hx => z.d_pos.trans hx))
    (fun x hx => congrFun (branchFinitePair_initial hs i z x hx) j)

lemma branchCorrection_periodic (j : Fin 2) :
    AngularPeriodic (2*Real.pi) (branchCorrection i z j) := by
  exact torusEndingCorrection_periodic
    (fun n x => congrFun (branchFinitePair_periodic_v i z n x) j)
    (torusAffineField_periodic _ _ _)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalChildTensor
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

lemma sourceChildTensorPush_mixed (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (y g v : Fin 3 → ℝ) :
    sourceScale^3 *
      ((fun i => sourceScale⁻¹*g (childAxis i)) ⬝ᵥ
        (sourceChildTensorPush k A (sourceChildCoordinates (actualChildSign k) y)*ᵥv))=
      g ⬝ᵥ (A y*ᵥ(fun i => sourceScale*v (childAxis i))) := by
  have he : (sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
  simp only [sourceChildTensorPush,he,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  have h₀ : childAxis 0=1 := rfl
  have h₁ : childAxis 1=0 := rfl
  have h₂ : childAxis 2=2 := rfl
  simp only [h₀,h₁,h₂]
  norm_num [sourceScale]
  ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalChildIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceChild_integral (σ : ℝ) {D : Set (Fin 3 → ℝ)}
    (hD : MeasurableSet D) (g : (Fin 3 → ℝ) → ℝ) :
    (∫ y in sourceChildCoordinates σ '' D,g y)=
      ∫ y in D,sourceScale^3*g (sourceChildCoordinates σ y) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hD
    (fun x _ => (sourceChildCoordinates_hasFDeriv σ x).hasFDerivWithinAt)
    (sourceChildHomeomorph σ).injective.injOn g
  change (∫ y in sourceChildCoordinates σ '' D,g y)=
    ∫ y in D,|sourceChildDerivative.det| • g (sourceChildCoordinates σ y) at h
  simpa only [sourceChildDerivative_det,abs_neg,abs_pow,
    abs_of_nonneg (show 0 ≤ sourceScale by norm_num [sourceScale]),smul_eq_mul] using h

lemma originalPiGradient_memLp_on_ball {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u : H1) (k : Fin 3) :
    MemLp (fun y => originalPiGradient u y k) 2 (volume.restrict D) := by
  have he := ballWholePiComponentCLM_ae_of_ae k.succ u.val
    (fun y => u.val (WithLp.toLp 2 y)) (by filter_upwards [] with x; rfl)
  apply MemLp.ae_eq ?_ ((Lp.memLp (ballWholePiComponentCLM k.succ u.val)).restrict D)
  filter_upwards [ae_restrict_of_ae he,ae_restrict_mem hD] with y hy hm
  rw [hy,ite_eq_left (hb y hm)]
  rfl

lemma originalPiGradient_eq_on_ball {D : Set (Fin 3 → ℝ)}
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u : H1)
    (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (he : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → ∀ k,
      weakGradient u x k=G (WithLp.ofLp x) k) :
    ∀ᵐ y : Fin 3 → ℝ,y∈D → originalPiGradient u y=G y := by
  have hh := (ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).mp he
  have hp := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae hh
  filter_upwards [hp] with y hy hm
  ext k
  exact hy (hb y hm) hm k

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalBlockTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal
attribute [local instance] OAI.ScalarConductivity.instMeasurableSpaceMatrixFinOfNatNatReal_solutions_1
local instance instBorelSpaceMatrixFinOfNatNatReal_solutions_1 : BorelSpace (Matrix (Fin 3) (Fin 3) ℝ) := ⟨rfl⟩

lemma sourceChildTensorPush_measurable (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (hA : Measurable A) :
    Measurable (sourceChildTensorPush k A) := by
  let F : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun M i j => sourceScale⁻¹*M (childAxis i) (childAxis j)
  have hc : Continuous F := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fun_prop
  have hm : Measurable F := hc.measurable
  exact hm.comp (hA.comp
    (sourceChildHomeomorph (actualChildSign k)).symm.continuous.measurable)

lemma physicalEndTensor_properties (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (i : Fin 3) :
    Measurable (physicalEndTensor s a i) ∧
      (∀ y,(physicalEndTensor s a i y).IsSymm) ∧
      (∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
        c*‖v‖^2 ≤ v ⬝ᵥ (physicalEndTensor s a i y*ᵥv) ∧
          v ⬝ᵥ (physicalEndTensor s a i y*ᵥv) ≤ C*‖v‖^2) ∧
      (∃ B : ℝ,0<B ∧ ∀ y,‖physicalEndTensor s a i y‖ ≤ B) := by
  refine Fin.cases ?_ (fun k => ?_) i
  · have hp := attachedCollarTensor_properties s hs (ha 0)
    exact ⟨hp.1,hp.2.1,hp.2.2.1,attachedFaceTensorList_bounded s (ha 0) _⟩
  · have hp := attachedCollarTensor_properties s hs (ha k.succ)
    obtain ⟨c,C,hc,hcC,h⟩ := hp.2.2.1
    obtain ⟨B,hB,hbound⟩ := attachedFaceTensorList_bounded s (ha k.succ)
      (Finset.univ : Finset (Fin 4 × Fin 4)).toList
    have hspos : 0 < sourceScale⁻¹ := by norm_num [sourceScale]
    refine ⟨sourceChildTensorPush_measurable k _ hp.1,
      sourceChildTensorPush_symmetric k _ hp.2.1,
      ⟨sourceScale⁻¹*c,sourceScale⁻¹*C,mul_pos hspos hc,
        mul_lt_mul_of_pos_left hcC hspos,?_⟩,
      ⟨|sourceScale⁻¹| * B,mul_pos (abs_pos.mpr hspos.ne') hB,
        sourceChildTensorPush_norm_bound k _ hB.le hbound⟩⟩
    intro y v
    change (sourceScale⁻¹*c)*‖v‖^2 ≤ v ⬝ᵥ (sourceChildTensorPush k _ y*ᵥv) ∧
      v ⬝ᵥ (sourceChildTensorPush k _ y*ᵥv) ≤ (sourceScale⁻¹*C)*‖v‖^2
    rw [sourceChildTensorPush_quadratic]
    have hh := h ((sourceChildHomeomorph (actualChildSign k)).symm y)
      (fun j => v (childAxis j))
    rw [childAxis_pi_norm] at hh
    exact ⟨by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.1 hspos.le,
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.2 hspos.le⟩

lemma physicalBlockTensorList_cons (s a : Fin 3 → ℝ) (i : Fin 3) (is : List (Fin 3))
    (y : Fin 3 → ℝ) : physicalBlockTensorList s a (i::is) y=
      (by classical exact if y∈physicalEndRegion i then physicalEndTensor s a i y
        else physicalBlockTensorList s a is y) := rfl

lemma physicalBlockTensorList_properties (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (is : List (Fin 3)) :
    Measurable (physicalBlockTensorList s a is) ∧
      (∀ y,(physicalBlockTensorList s a is y).IsSymm) ∧
      (∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
        c*‖v‖^2 ≤ v ⬝ᵥ (physicalBlockTensorList s a is y*ᵥv) ∧
          v ⬝ᵥ (physicalBlockTensorList s a is y*ᵥv) ≤ C*‖v‖^2) ∧
      (∃ B : ℝ,0<B ∧ ∀ y,‖physicalBlockTensorList s a is y‖ ≤ B) := by
  classical
  induction is with
  | nil =>
    obtain ⟨c,C,hc,hcC,h⟩ := identity_matrix_energy_bounds
    exact ⟨measurable_const,fun _ => Matrix.transpose_one,
      ⟨c,C,hc,hcC,fun _ => h⟩,
      ⟨‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖+1,by positivity,fun _ => by
        change ‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖ ≤ _; linarith⟩⟩
  | cons i is ih =>
    have hi := physicalEndTensor_properties s a hs ha i
    obtain ⟨c,C,hc,hcC,h⟩ := ih.2.2.1
    obtain ⟨d,D,hd,hdD,hlocal⟩ := hi.2.2.1
    obtain ⟨B,hB,hbound⟩ := ih.2.2.2
    obtain ⟨E,hE,hend⟩ := hi.2.2.2
    refine ⟨Measurable.ite (physicalEndRegion_compact i).measurableSet hi.1 ih.1,?_,
      ⟨min c d,max C D,lt_min hc hd,
        lt_of_le_of_lt (min_le_left _ _) (hcC.trans_le (le_max_left _ _)),?_⟩,
      ⟨max B E,hB.trans_le (le_max_left _ _),?_⟩⟩
    · intro y
      rw [physicalBlockTensorList_cons]
      split_ifs
      · exact hi.2.1 y
      · exact ih.2.1 y
    · intro y v
      rw [physicalBlockTensorList_cons]
      split_ifs with hy
      · exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
          (hlocal y v).1,(hlocal y v).2.trans
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))⟩
      · exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
          (h y v).1,(h y v).2.trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩
    · intro y
      rw [physicalBlockTensorList_cons]
      split_ifs
      · exact (hend y).trans (le_max_right _ _)
      · exact (hbound y).trans (le_max_left _ _)

lemma physicalBlockTensor_local_list (s a : Fin 3 → ℝ) (is : List (Fin 3))
    (i : Fin 3) (hi : i∈is) {y : Fin 3 → ℝ} (hy : y∈physicalEndRegion i) :
    physicalBlockTensorList s a is y=physicalEndTensor s a i y := by
  classical
  induction is with
  | nil => simp at hi
  | cons j is ih =>
    rw [physicalBlockTensorList_cons]
    by_cases he : j=i
    · subst j; simp only [ite_eq_left hy]
    · have hn : y∉physicalEndRegion j := fun hj =>
        (disjoint_left.mp (physicalEndRegion_pairwise_disjoint he) hj hy)
      rw [ite_eq_right hn]
      exact ih ((List.mem_cons.mp hi).resolve_left (Ne.symm he))

lemma physicalBlockTensor_local (s a : Fin 3 → ℝ) (i : Fin 3)
    {y : Fin 3 → ℝ} (hy : y∈physicalEndRegion i) :
    physicalBlockTensor s a y=physicalEndTensor s a i y :=
  physicalBlockTensor_local_list s a _ i (by simp) hy

lemma physicalBlockTensorList_outside (s a : Fin 3 → ℝ) (is : List (Fin 3))
    {y : Fin 3 → ℝ} (hy : ∀ i∈is,y∉physicalEndRegion i) :
    physicalBlockTensorList s a is y=1 := by
  classical
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [physicalBlockTensorList_cons,ite_eq_right (hy i List.mem_cons_self)]
    exact ih (fun j hj => hy j (List.mem_cons_of_mem i hj))

theorem physicalBlockTensor_properties (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) :
    Measurable (physicalBlockTensor s a) ∧
      MemLp (physicalBlockTensor s a) ∞ (volume : Measure (Fin 3 → ℝ)) ∧
      (∀ y,(physicalBlockTensor s a y).IsSymm) ∧
      (∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
        c*‖v‖^2 ≤ v ⬝ᵥ (physicalBlockTensor s a y*ᵥv) ∧
          v ⬝ᵥ (physicalBlockTensor s a y*ᵥv) ≤ C*‖v‖^2) ∧
      (∀ i y,y∈physicalEndRegion i → physicalBlockTensor s a y=physicalEndTensor s a i y) ∧
      (∀ y,(∀ i,y∉physicalEndRegion i) → physicalBlockTensor s a y=1) := by
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))
  let : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  have h := physicalBlockTensorList_properties s a hs ha
    (Finset.univ : Finset (Fin 3)).toList
  obtain ⟨B,hB,hbound⟩ := h.2.2.2
  exact ⟨h.1,memLp_top_of_bound h.1.aestronglyMeasurable B (ae_of_all _ hbound),
    h.2.1,h.2.2.1,fun i y hy => physicalBlockTensor_local s a i hy,
    fun y hy => physicalBlockTensorList_outside s a _ (fun i _ => hy i)⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma physicalBlockTensor_central_ae (s a : Fin 3 → ℝ) :
    ∀ᵐ y∂(volume : Measure (Fin 3 → ℝ)),y∈centralPhysical → physicalBlockTensor s a y=1 := by
  have hparent := sourceColevel_ae_ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
  have hchild (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae
    (sourceColevel_ae_ne
      (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness]))
  filter_upwards [hparent,hchild 0,hchild 1] with y hp hc₀ hc₁ hy
  apply physicalBlockTensorList_outside
  intro i _ hi
  have ht := (centralPhysical_time_iff y).mp hy
  have hn (k : Fin 2) : sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y)≠-centralThickness := by
    fin_cases k
    · exact hc₀
    · exact hc₁
  fin_cases i
  · change sourceCollarTime y∈Icc 0 centralThickness at hi
    exact hp (le_antisymm hi.2 ht.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hn 0 (le_antisymm (ht.2 0) hi.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hn 1 (le_antisymm (ht.2 1) hi.1)

lemma physicalBlockTensor_entry_memLp (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (i j : Fin 3) :
    MemLp (fun y => physicalBlockTensor s a y i j) ∞
      (volume : Measure (Fin 3 → ℝ)) := by
  have h := physicalBlockTensor_properties s a hs ha
  let heval : (Matrix (Fin 3) (Fin 3) ℝ) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.proj j) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
      ((ContinuousLinearMap.proj i) : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 3 → ℝ))
  exact heval.comp_memLp' h.2.1

theorem physicalBlockTensor_weak_integrable (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u v : H1) :
    Integrable (fun y => originalPiGradient u y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y)) (volume.restrict D) := by
  have hrow (i : Fin 3) : MemLp (fun y => ∑ j : Fin 3,
      physicalBlockTensor s a y i j*originalPiGradient v y j) 2 (volume.restrict D) := by
    apply memLp_finsetSum
    intro j _
    exact (originalPiGradient_memLp_on_ball hD hb v j).mul (r := 2)
      ((physicalBlockTensor_entry_memLp s a hs ha i j).restrict D)
  change Integrable (fun y => ∑ i : Fin 3,originalPiGradient u y i*
    ∑ j : Fin 3,physicalBlockTensor s a y i j*originalPiGradient v y j) _
  apply integrable_finsetSum
  intro i _
  exact (originalPiGradient_memLp_on_ball hD hb u i).integrable_mul (hrow i)

lemma physicalBlockTensor_end_energy (s a : Fin 3 → ℝ) (i : Fin 3)
    {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D) (hsub : D⊆physicalEndRegion i)
    (u v : H1) :
    (∫ y in D,originalPiGradient u y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))=
    ∫ y in D,originalPiGradient u y ⬝ᵥ
      (physicalEndTensor s a i y*ᵥoriginalPiGradient v y) := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hD] with y hy
  rw [physicalBlockTensor_local s a i (hsub hy)]

lemma physicalBlockTensor_central_energy (s a : Fin 3 → ℝ) (u v : H1) :
    (∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))=
    ∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ originalPiGradient v y := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (physicalBlockTensor_central_ae s a),
    ae_restrict_mem centralPhysical_compact.measurableSet] with y he hy
  rw [he hy,Matrix.one_mulVec]

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma physicalBlockRegion_compact : IsCompact physicalBlockRegion :=
  centralPhysical_compact.union (isCompact_iUnion physicalEndRegion_compact)

lemma physicalBlockRegion_subset_ball {y : Fin 3 → ℝ} (hy : y∈physicalBlockRegion) :
    WithLp.toLp 2 y∈ball := by
  rcases hy with hc|he
  · exact centralPhysical_subset_ball hc
  · obtain ⟨i,hi⟩ := mem_iUnion.mp he
    exact physicalEndRegion_subset_ball i hi

lemma physicalEndRegion_mem_block (i : Fin 3) : physicalEndRegion i⊆physicalBlockRegion :=
  fun _ hy => Or.inr (mem_iUnion.mpr ⟨i,hy⟩)

lemma physicalBlockRegion_central_end_exclusive_ae :
    ∀ᵐ y∂(volume : Measure (Fin 3 → ℝ)),
      y∈centralPhysical → ∀ i : Fin 3,y∉physicalEndRegion i := by
  have hparent := sourceColevel_ae_ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
  have hchild (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae
    (sourceColevel_ae_ne
      (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness]))
  filter_upwards [hparent,hchild 0,hchild 1] with y hp hc₀ hc₁ hy i hi
  have ht := (centralPhysical_time_iff y).mp hy
  fin_cases i
  · change sourceCollarTime y∈Icc 0 centralThickness at hi
    exact hp (le_antisymm hi.2 ht.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hc₀ (le_antisymm (ht.2 0) hi.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hc₁ (le_antisymm (ht.2 1) hi.1)

lemma physicalBlockRegion_indicator_ae (f : (Fin 3 → ℝ) → ℝ) :
    physicalBlockRegion.indicator f=ᵐ[volume]
      (fun y => centralPhysical.indicator f y+
        ∑ i : Fin 3,(physicalEndRegion i).indicator f y) := by
  classical
  filter_upwards [physicalBlockRegion_central_end_exclusive_ae] with y he
  by_cases hc : y∈centralPhysical
  · have hb : y∈physicalBlockRegion := Or.inl hc
    rw [indicator_of_mem hb,indicator_of_mem hc]
    have hsum : (∑ i : Fin 3,(physicalEndRegion i).indicator f y)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (he hc i) _
    rw [hsum,add_zero]
  · rw [indicator_of_notMem hc]
    by_cases hend : ∃ i : Fin 3,y∈physicalEndRegion i
    · obtain ⟨i,hi⟩ := hend
      have hb : y∈physicalBlockRegion := physicalEndRegion_mem_block i hi
      rw [indicator_of_mem hb,zero_add]
      symm
      calc
        _ = (physicalEndRegion i).indicator f y := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            exact indicator_of_notMem (fun hj =>
              disjoint_left.mp (physicalEndRegion_pairwise_disjoint hji) hj hi) _
          · simp
        _ = f y := indicator_of_mem hi f
    · have hb : y∉physicalBlockRegion := by
        rintro (hh|hh)
        · exact hc hh
        · exact hend (mem_iUnion.mp hh)
      rw [indicator_of_notMem hb,zero_add]
      symm
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (fun hi => hend ⟨i,hi⟩) _

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockEnergySum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma physicalBlockRegion_integral (f : (Fin 3 → ℝ) → ℝ)
    (hc : IntegrableOn f centralPhysical volume)
    (he : ∀ i : Fin 3,IntegrableOn f (physicalEndRegion i) volume) :
    (∫ y in physicalBlockRegion,f y)=(∫ y in centralPhysical,f y)+
      ∑ i : Fin 3,∫ y in physicalEndRegion i,f y := by
  have hci := hc.integrable_indicator centralPhysical_compact.measurableSet
  have hei (i : Fin 3) := (he i).integrable_indicator (physicalEndRegion_compact i).measurableSet
  rw [←integral_indicator physicalBlockRegion_compact.measurableSet]
  rw [integral_congr_ae (physicalBlockRegion_indicator_ae f)]
  rw [integral_add hci (integrable_finsetSum _ (fun i _ => hei i)),
    integral_finsetSum _ (fun i _ => hei i),
    integral_indicator centralPhysical_compact.measurableSet]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_indicator (physicalEndRegion_compact i).measurableSet

theorem physicalBlockTensor_energy_sum (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (u v : H1) :
    Integrable (fun y => originalPiGradient u y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y)) (volume.restrict physicalBlockRegion) ∧
    (∫ y in physicalBlockRegion,originalPiGradient u y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))=
      (∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ originalPiGradient v y)+
      ∑ i : Fin 3,∫ y in physicalEndRegion i,originalPiGradient u y ⬝ᵥ
        (physicalEndTensor s a i y*ᵥoriginalPiGradient v y) := by
  refine ⟨physicalBlockTensor_weak_integrable s a hs ha
    physicalBlockRegion_compact.measurableSet (fun _ => physicalBlockRegion_subset_ball) u v,?_⟩
  rw [physicalBlockRegion_integral _
    (physicalBlockTensor_weak_integrable s a hs ha centralPhysical_compact.measurableSet
      (fun _ => centralPhysical_subset_ball) u v)
    (fun i => physicalBlockTensor_weak_integrable s a hs ha
      (physicalEndRegion_compact i).measurableSet
        (fun _ => physicalEndRegion_subset_ball i) u v),
    physicalBlockTensor_central_energy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact physicalBlockTensor_end_energy s a i (physicalEndRegion_compact i).measurableSet
    Subset.rfl u v

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceExpandedInner_bounds {y : Fin 3 → ℝ}
    (hy : -centralThickness ≤ sourceCollarTime y) :
    |y 0|≤1602/1000 ∧ |y 1|≤1001/1000 ∧ |y 2|≤1002/1000 := by
  have hh := (sourceCollarTime_ge_iff y (-centralThickness)).mp hy
  have hx := (le_max_left (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  have hy' := (le_max_right (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  norm_num [centralThickness,sourceRadialWidth,sourceHole,sourceLength] at hx hy' hh ⊢
  exact ⟨by linarith,by linarith,by linarith [hh.1]⟩

lemma sourceExpandedChild_far_parent (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : -centralThickness ≤ sourceCollarTime y) :
    2*centralThickness ≤ sourceCollarTime (sourceChildCoordinates (actualChildSign k) y) := by
  obtain ⟨h₀,h₁,h₂⟩ := sourceExpandedInner_bounds hy
  have hsign : |actualChildSign k|=1 := by fin_cases k <;> norm_num [actualChildSign]
  have ha : |actualChildSign k*sourceOffset|=sourceOffset := by
    rw [abs_mul,hsign,one_mul]; norm_num [sourceOffset]
  have hu := abs_add_le (sourceScale*y 1) (actualChildSign k*sourceOffset)
  rw [abs_mul,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale]),ha] at hu
  have hl := abs_add_le (-sourceScale*y 1) (sourceScale*y 1+actualChildSign k*sourceOffset)
  have he : -sourceScale*y 1+(sourceScale*y 1+actualChildSign k*sourceOffset)=
    actualChildSign k*sourceOffset := by ring
  rw [he,ha,abs_mul,abs_neg,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])] at hl
  apply (sourceCollarTime_ge_iff _ _).mpr
  change |sourceScale*y 2|≤_ ∧ _≤ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
    (|sourceScale*y 0|) ∧ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
      (|sourceScale*y 0|)≤_
  simp only [abs_mul,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])]
  constructor
  · norm_num [sourceScale,centralThickness]; linarith
  · constructor
    · apply le_trans _ (le_max_left _ _)
      norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
      linarith
    · apply max_le
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith

lemma sourceExpandedChildren_exclusive (y : Fin 3 → ℝ)
    (h₀ : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y))
    (h₁ : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)) : False := by
  have ha := (sourceExpandedInner_bounds h₀).2.1
  have hb := (sourceExpandedInner_bounds h₁).2.1
  change |(y 0 - actualChildSign 0 * sourceOffset)/sourceScale| ≤ _ at ha
  change |(y 0 - actualChildSign 1 * sourceOffset)/sourceScale| ≤ _ at hb
  norm_num [actualChildSign] at ha hb
  rw [abs_div,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])] at ha hb
  have ha' := abs_le.mp ((div_le_iff₀ (show 0 < sourceScale by norm_num [sourceScale])).mp ha)
  have hb' := abs_le.mp ((div_le_iff₀ (show 0 < sourceScale by norm_num [sourceScale])).mp hb)
  norm_num [sourceScale,sourceOffset] at ha' hb'
  linarith [ha'.1,hb'.2]

lemma sourceExpandedChild_other (k j : Fin 2) (hkj : k≠j) {y : Fin 3 → ℝ}
    (hy : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)) :
    sourceCollarTime ((sourceChildHomeomorph (actualChildSign j)).symm y)< -centralThickness := by
  by_contra h
  have hj := le_of_not_gt h
  fin_cases k <;> fin_cases j
  · exact hkj rfl
  · exact sourceExpandedChildren_exclusive y hy hj
  · exact sourceExpandedChildren_exclusive y hj hy
  · exact hkj rfl

theorem physicalBlockRegion_time_iff (y : Fin 3 → ℝ) :
    y∈physicalBlockRegion ↔ 0≤ sourceCollarTime y ∧
      ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)≤0 := by
  have hδ : 0 < centralThickness := by norm_num [centralThickness]
  have hfar (k : Fin 2)
      (h : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)) :
      2*centralThickness≤ sourceCollarTime y := by
    have hh := sourceExpandedChild_far_parent k h
    have he : sourceChildCoordinates (actualChildSign k)
        ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
      (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
    rwa [he] at hh
  constructor
  · rintro (hc|he)
    · obtain ⟨hp,hc⟩ := (centralPhysical_time_iff y).mp hc
      exact ⟨hδ.le.trans hp,fun k => (hc k).trans (by linarith)⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp he
      revert hi
      refine Fin.cases ?_ (fun k => ?_) i
      · intro hi
        change sourceCollarTime y∈Icc 0 centralThickness at hi
        refine ⟨hi.1,fun k => ?_⟩
        by_contra hn
        have hh := hfar k (show -centralThickness≤ sourceCollarTime
            ((sourceChildHomeomorph (actualChildSign k)).symm y) by linarith [lt_of_not_ge hn])
        linarith [hi.2]
      · intro hi
        change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)
          ∈Icc (-centralThickness) 0 at hi
        refine ⟨(by linarith [hfar k hi.1]),fun j => ?_⟩
        by_cases hkj : k=j
        · simpa only [←hkj] using hi.2
        · exact (sourceExpandedChild_other k j hkj hi.1).le.trans (by linarith)
  · rintro ⟨hp,hc⟩
    by_cases ht : sourceCollarTime y ≤ centralThickness
    · exact physicalEndRegion_mem_block 0 ⟨hp,ht⟩
    · by_cases hh : ∀ k : Fin 2,sourceCollarTime
          ((sourceChildHomeomorph (actualChildSign k)).symm y)≤ -centralThickness
      · exact Or.inl ((centralPhysical_time_iff y).mpr ⟨(lt_of_not_ge ht).le,hh⟩)
      · push Not at hh
        obtain ⟨k,hk⟩ := hh
        exact physicalEndRegion_mem_block k.succ ⟨hk.le,hc k⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_PhysicalBlockDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceCollarTime_pos_iff_domain (y : Fin 3 → ℝ) :
    0 < sourceCollarTime y ↔ WithLp.toLp 2 y∈sourceDomain := by
  change 0 < sourceCollarTime y ↔ sourceHole < sourceRadial y ∧ sourceRadial y<1 ∧ |y 2|<1
  rw [←not_le,sourceCollarTime_le_iff]
  simp only [sub_zero,mul_zero,add_zero,not_or,not_le]
  tauto

lemma sourceDomain_closure_time (y : Fin 3 → ℝ) :
    WithLp.toLp 2 y∈closure sourceDomain ↔ 0≤ sourceCollarTime y := by
  have hcoord : Continuous (fun x : R3 => (fun i : Fin 3 => x i)) :=
    continuous_pi (fun i => (EuclideanSpace.proj i).continuous)
  have hclosed : IsClosed {x : R3 | 0≤ sourceCollarTime (fun i => x i)} :=
    isClosed_le continuous_const (locallyLipschitz_sourceCollarTime.continuous.comp hcoord)
  constructor
  · intro hy
    exact closure_minimal (fun x hx => ((sourceCollarTime_pos_iff_domain _).mpr hx).le) hclosed hy
  · intro hy
    by_cases hp : 0 < sourceCollarTime y
    · exact subset_closure ((sourceCollarTime_pos_iff_domain y).mp hp)
    · have he : sourceCollarTime y=0 := le_antisymm (le_of_not_gt hp) hy
      let g : ℝ → R3 := fun t => WithLp.toLp 2 (sourceAngularCollar t (sourcePhysicalAngles y))
      have hg : Continuous g := (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
        (continuous_uncurry_sourceAngularCollar.comp (continuous_id.prodMk continuous_const))
      have hz : (0:ℝ)∈closure (Ioo 0 centralThickness) := by
        rw [closure_Ioo (show (0:ℝ)≠centralThickness by norm_num [centralThickness])]
        exact ⟨le_rfl,by norm_num [centralThickness]⟩
      have hin : g '' Ioo 0 centralThickness ⊆ sourceDomain := by
        rintro _ ⟨t,ht,rfl⟩
        apply (sourceCollarTime_pos_iff_domain _).mp
        rw [sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
          ⟨by linarith [ht.1],ht.2.le.trans (by norm_num [centralThickness])⟩)]
        exact ht.1
      have hmem := closure_mono hin (image_closure_subset_closure_image hg ⟨0,hz,rfl⟩)
      have hright := sourcePhysicalCoordinates_right
        (show sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100) by rw [he]; norm_num)
      rw [he] at hright
      simpa only [g,hright] using hmem

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalOpenBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceSimilarity_childInverse (σ : ℝ) (y : Fin 3 → ℝ) :
    sourceSimilarity σ (WithLp.toLp 2 ((sourceChildHomeomorph σ).symm y))=WithLp.toLp 2 y := by
  rw [←sourceChild_toLp]
  exact congrArg (WithLp.toLp 2) ((sourceChildHomeomorph σ).apply_symm_apply y)

lemma sourceChild_closure_image_iff (σ : ℝ) (y : Fin 3 → ℝ) :
    WithLp.toLp 2 y∈sourceSimilarity σ '' closure sourceDomain ↔
      0≤ sourceCollarTime ((sourceChildHomeomorph σ).symm y) := by
  rw [←sourceDomain_closure_time]
  constructor
  · rintro ⟨x,hx,he⟩
    have hh := (sourceSimilarity σ).injective (he.trans (sourceSimilarity_childInverse σ y).symm)
    rwa [←hh]
  · intro hy
    exact ⟨_,hy,sourceSimilarity_childInverse σ y⟩

lemma sourceOpenBlock_time_iff (y : Fin 3 → ℝ) :
    WithLp.toLp 2 y∈sourceOpenBlock ↔ 0 < sourceCollarTime y ∧
      ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)<0 := by
  simp only [sourceOpenBlock,Set.mem_sdiff,mem_iUnion,not_exists,
    ←sourceCollarTime_pos_iff_domain,sourceChild_closure_image_iff,not_le]

lemma physicalBlockRegion_openBlock_ae :
    physicalBlockRegion=ᵐ[volume] ((WithLp.toLp 2) ⁻¹' sourceOpenBlock) := by
  have hparent := sourceColevel_ae_ne (show (0:ℝ)∈Icc (-(1:ℝ)/100) (1/100) by norm_num)
  have hchild (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae hparent
  filter_upwards [hparent,hchild 0,hchild 1] with y hp hc₀ hc₁
  apply propext
  change y∈physicalBlockRegion ↔ y∈((WithLp.toLp 2) ⁻¹' sourceOpenBlock)
  rw [physicalBlockRegion_time_iff,mem_preimage,sourceOpenBlock_time_iff]
  have hc (k : Fin 2) : sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)≠0 := by
    fin_cases k
    · exact hc₀
    · exact hc₁
  constructor
  · rintro ⟨hp',hc'⟩
    exact ⟨lt_of_le_of_ne hp' hp.symm,fun k => lt_of_le_of_ne (hc' k) (hc k)⟩
  · rintro ⟨hp',hc'⟩
    exact ⟨hp'.le,fun k => (hc' k).le⟩

lemma physicalBlockRegion_openBlock_restrict :
    (volume : Measure (Fin 3 → ℝ)).restrict physicalBlockRegion=
      volume.restrict ((WithLp.toLp 2) ⁻¹' sourceOpenBlock) :=
  Measure.restrict_congr_set physicalBlockRegion_openBlock_ae

end ScalarConductivity



end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceOpenBlock_parent_band {y : Fin 3 → ℝ}
    (hp : 0 < sourceCollarTime y) (ht : sourceCollarTime y < centralThickness) :
    WithLp.toLp 2 y∈sourceOpenBlock := by
  apply (sourceOpenBlock_time_iff y).mpr
  refine ⟨hp,fun k => ?_⟩
  by_contra hn
  have hc : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y) :=
    (show -centralThickness≤(0:ℝ) by norm_num [centralThickness]).trans (le_of_not_gt hn)
  have hfar := sourceExpandedChild_far_parent k hc
  have he : sourceChildCoordinates (actualChildSign k)
      ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
  rw [he] at hfar
  norm_num [centralThickness] at ht hfar
  linarith

lemma sourceOpenBlock_child_band (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : -centralThickness ≤ sourceCollarTime y) (ht : sourceCollarTime y<0) :
    WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) y)∈sourceOpenBlock := by
  apply (sourceOpenBlock_time_iff _).mpr
  refine ⟨lt_of_lt_of_le (show (0:ℝ)<2*centralThickness by norm_num [centralThickness])
    (sourceExpandedChild_far_parent k hy),fun j => ?_⟩
  have he : (sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
  by_cases hkj : k=j
  · rw [←hkj,he]
    exact ht
  · exact (sourceExpandedChild_other k j hkj (show -centralThickness ≤ sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm
        (sourceChildCoordinates (actualChildSign k) y)) by rw [he]; exact hy)).trans
      (by norm_num [centralThickness])

lemma physicalBlockRegion_mem_closure_openBlock {y : Fin 3 → ℝ}
    (hy : y∈physicalBlockRegion) :
    y∈closure ((WithLp.toLp 2) ⁻¹' sourceOpenBlock) := by
  obtain ⟨hp,hc⟩ := (physicalBlockRegion_time_iff y).mp hy
  by_cases h0 : sourceCollarTime y=0
  · let g : ℝ → (Fin 3 → ℝ) := fun t => sourceAngularCollar t (sourcePhysicalAngles y)
    have hg : Continuous g := continuous_uncurry_sourceAngularCollar.comp
      (continuous_id.prodMk continuous_const)
    have hz : (0:ℝ)∈closure (Ioo 0 centralThickness) := by
      rw [closure_Ioo (show (0:ℝ)≠centralThickness by norm_num [centralThickness])]
      exact ⟨le_rfl,by norm_num [centralThickness]⟩
    have hin : g '' Ioo 0 centralThickness ⊆ (WithLp.toLp 2) ⁻¹' sourceOpenBlock := by
      rintro _ ⟨t,ht,rfl⟩
      have he := sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
        ⟨by linarith [ht.1],ht.2.le.trans (by norm_num [centralThickness])⟩) (sourcePhysicalAngles y)
      exact sourceOpenBlock_parent_band (by dsimp [g]; rw [he]; exact ht.1) (by dsimp [g]; rw [he]; exact ht.2)
    have hmem := closure_mono hin (image_closure_subset_closure_image hg ⟨0,hz,rfl⟩)
    have he := sourcePhysicalCoordinates_right
      (show sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100) by rw [h0]; norm_num)
    rw [h0] at he
    simpa only [g,he] using hmem
  · by_cases hchild : ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)≠0
    · exact subset_closure ((sourceOpenBlock_time_iff y).mpr
        ⟨lt_of_le_of_ne hp (Ne.symm h0),fun k => lt_of_le_of_ne (hc k) (hchild k)⟩)
    · push Not at hchild
      obtain ⟨k,hk⟩ := hchild
      let z := (sourceChildHomeomorph (actualChildSign k)).symm y
      let g : ℝ → (Fin 3 → ℝ) := fun t => sourceChildCoordinates (actualChildSign k)
        (sourceAngularCollar t (sourcePhysicalAngles z))
      have hg : Continuous g := (sourceChildCoordinates_contDiff _).continuous.comp
        (continuous_uncurry_sourceAngularCollar.comp (continuous_id.prodMk continuous_const))
      have hz : (0:ℝ)∈closure (Ioo (-centralThickness) 0) := by
        rw [closure_Ioo (show -centralThickness≠(0:ℝ) by norm_num [centralThickness])]
        exact ⟨by norm_num [centralThickness],le_rfl⟩
      have hin : g '' Ioo (-centralThickness) 0 ⊆ (WithLp.toLp 2) ⁻¹' sourceOpenBlock := by
        rintro _ ⟨t,ht,rfl⟩
        apply sourceOpenBlock_child_band k
        · rw [sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
            ⟨(show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans ht.1.le,
              ht.2.le.trans (by norm_num)⟩)]
          exact ht.1.le
        · rw [sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
            ⟨(show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans ht.1.le,
              ht.2.le.trans (by norm_num)⟩)]
          exact ht.2
      have hmem := closure_mono hin (image_closure_subset_closure_image hg ⟨0,hz,rfl⟩)
      have he := sourcePhysicalCoordinates_right
        (show sourceCollarTime z∈Icc (-(1:ℝ)/100) (1/100) by
          change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)∈_
          rw [hk]
          norm_num)
      change sourceAngularCollar (sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y))
        (sourcePhysicalAngles z)=z at he
      rw [hk] at he
      have he' : sourceChildCoordinates (actualChildSign k) z=y :=
        (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
      simpa only [g,he,he'] using hmem

theorem physicalBlockRegion_eq_closure_openBlock : physicalBlockRegion=
    closure ((WithLp.toLp 2) ⁻¹' sourceOpenBlock) := by
  apply Subset.antisymm (fun y hy => physicalBlockRegion_mem_closure_openBlock hy)
  apply closure_minimal _ physicalBlockRegion_compact.isClosed
  intro y hy
  obtain ⟨hp,hc⟩ := (sourceOpenBlock_time_iff y).mp hy
  exact (physicalBlockRegion_time_iff y).mpr ⟨hp.le,fun k => (hc k).le⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPhysicalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma centralPhysicalWholeCLM_ae (f : CentralL2) :
    centralPhysicalWholeCLM f=ᵐ[volume]
      (fun y => centralPhysical.indicator (fun y => f (sourcePairCoordinates y)) y) := by
  apply (Lp.coeFn_compMeasurePreserving _ sourcePair_volume).trans
  have he := sourcePair_volume.quasiMeasurePreserving.ae_eq_comp
    (lpZeroExtensionCLM_ae centralClosed_compact.measurableSet f)
  apply he.trans
  filter_upwards [] with y
  by_cases h : sourcePairCoordinates y∈centralClosed <;>
    simp [sourcePairMeasurable_apply,centralPhysical,h]
  rfl

lemma centralPhysicalWholeCLM_integral (f g : CentralL2) :
    IntegrableOn (fun y => centralPhysicalWholeCLM f y*centralPhysicalWholeCLM g y)
      centralPhysical volume ∧
    (∫ y in centralPhysical,centralPhysicalWholeCLM f y*centralPhysicalWholeCLM g y)=
      inner ℝ f g := by
  have hi := (Lp.memLp (centralPhysicalWholeCLM f)).integrable_mul
    (Lp.memLp (centralPhysicalWholeCLM g))
  refine ⟨hi.integrableOn,?_⟩
  rw [←centralPhysicalWholeLI.inner_map_map f g,L2.inner_def,
    ←integral_indicator centralPhysical_compact.measurableSet]
  apply integral_congr_ae
  filter_upwards [centralPhysicalWholeCLM_ae f,centralPhysicalWholeCLM_ae g] with y hf hg
  change centralPhysical.indicator
    (fun y => centralPhysicalWholeCLM f y*centralPhysicalWholeCLM g y) y=
      inner ℝ (centralPhysicalWholeCLM f y) (centralPhysicalWholeCLM g y)
  rw [Real.inner_apply]
  by_cases hy : y∈centralPhysical
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy,hf,hg,indicator_of_notMem hy,indicator_of_notMem hy]; ring

lemma H1JetOn.central_gradient {s : Fin 3 → ℝ} {p : centralEnergySpace s} {w : H1}
    (hw : H1JetOn w centralPhysical (centralFullJetCLM s p.val)) :
    ∀ᵐ y : Fin 3 → ℝ,y∈centralPhysical → originalPiGradient w y=
      (fun i : Fin 3 => centralPhysicalWholeCLM (centralAmbientComponent s i.succ p.val) y) := by
  apply originalPiGradient_eq_on_ball (fun _ => centralPhysical_subset_ball) w _
  filter_upwards [hw,physicalFourJetCLM_ae
    (fun i => centralPhysicalWholeCLM (centralAmbientComponent s i p.val))] with x hx he hy
  have h := (hx hy).trans he
  intro i
  exact congrArg (fun v : JetFiber => v i.succ) h

lemma central_physical_energy {s : Fin 3 → ℝ} (p q : centralEnergySpace s) (w v : H1)
    (hw : H1JetOn w centralPhysical (centralFullJetCLM s p.val))
    (hv : H1JetOn v centralPhysical (centralFullJetCLM s q.val)) :
    (∫ y in centralPhysical,originalPiGradient w y ⬝ᵥ originalPiGradient v y)=
      inner ℝ (centralD s p) (centralD s q) := by
  calc
    _ = ∫ y in centralPhysical,∑ i : Fin 3,
        centralPhysicalWholeCLM (centralAmbientComponent s i.succ p.val) y*
          centralPhysicalWholeCLM (centralAmbientComponent s i.succ q.val) y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hw.central_gradient,ae_restrict_of_ae hv.central_gradient,
        ae_restrict_mem centralPhysical_compact.measurableSet] with y hp hq hy
      rw [hp hy,hq hy]
      rfl
    _ = ∑ i : Fin 3,inner ℝ (centralAmbientComponent s i.succ p.val)
        (centralAmbientComponent s i.succ q.val) := by
      rw [integral_finsetSum (f:=fun i : Fin 3 => fun y =>
        centralPhysicalWholeCLM (centralAmbientComponent s i.succ p.val) y*
          centralPhysicalWholeCLM (centralAmbientComponent s i.succ q.val) y) Finset.univ (fun i _ =>
        (centralPhysicalWholeCLM_integral (centralAmbientComponent s i.succ p.val)
          (centralAmbientComponent s i.succ q.val)).1)]
      exact Finset.sum_congr rfl (fun i _ =>
        (centralPhysicalWholeCLM_integral (centralAmbientComponent s i.succ p.val)
          (centralAmbientComponent s i.succ q.val)).2)
    _ = _ := by rw [PiLp.inner_apply]; rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceJoin_children_separate (k l : Fin 2) (hkl : k≠l) {y : Fin 3 → ℝ}
    (hk : -2*centralThickness ≤ sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y))
    (hl : -2*centralThickness ≤ sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign l)).symm y)) : False := by
  have h₁ := (sourceJoinInner_bounds hk).2.1
  have h₂ := (sourceJoinInner_bounds hl).2.1
  change |(y 0-actualChildSign k*sourceOffset)/sourceScale|≤1002/1000 at h₁
  change |(y 0-actualChildSign l*sourceOffset)/sourceScale|≤1002/1000 at h₂
  rw [abs_div,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])] at h₁ h₂
  have h₁' := abs_le.mp ((div_le_iff₀ (show 0 < sourceScale by norm_num [sourceScale])).mp h₁)
  have h₂' := abs_le.mp ((div_le_iff₀ (show 0 < sourceScale by norm_num [sourceScale])).mp h₂)
  fin_cases k <;> fin_cases l
  · exact hkl rfl
  · norm_num [actualChildSign,sourceScale,sourceOffset] at h₁' h₂'
    linarith [h₁'.1,h₂'.2]
  · norm_num [actualChildSign,sourceScale,sourceOffset] at h₁' h₂'
    linarith [h₂'.1,h₁'.2]
  · exact hkl rfl

lemma physicalOtherEnd_child_time (k : Fin 2) (i : Fin 3) (hik : i≠k.succ)
    {y : Fin 3 → ℝ} (hy : y∈physicalEndRegion i) :
    sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)< -2*centralThickness := by
  by_contra hn
  have ht := le_of_not_gt hn
  revert hy hik
  refine Fin.cases ?_ (fun l => ?_) i
  · intro _ hy
    have hh := sourceJoinChild_far_parent k ht
    have he : sourceChildCoordinates (actualChildSign k)
        ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
      (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
    rw [he] at hh
    change sourceCollarTime y∈Icc 0 centralThickness at hy
    norm_num [centralThickness] at hh hy
    linarith [hy.2]
  · intro hik hy
    have hl : -2*centralThickness ≤ sourceCollarTime
        ((sourceChildHomeomorph (actualChildSign l)).symm y) := by
      change sourceCollarTime ((sourceChildHomeomorph (actualChildSign l)).symm y)
        ∈Icc (-centralThickness) 0 at hy
      have := hy.1
      dsimp [centralThickness] at *
      linarith
    exact sourceJoin_children_separate k l (fun he => hik (congrArg Fin.succ he.symm)) ht hl

lemma physicalChildEnd_parent_time (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : y∈physicalEndRegion k.succ) : 2*centralThickness ≤ sourceCollarTime y := by
  have hh := physicalChildEnd_far_parent k hy
  have he : sourceChildCoordinates (actualChildSign k)
      ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
  rwa [he] at hh

end ScalarConductivity
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalSmoothTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma piSmoothH1_gradient {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {D : Set (Fin 3 → ℝ)} (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) :
    ∀ᵐ y : Fin 3 → ℝ,y∈D → originalPiGradient (piSmoothH1 hφ) y=physicalTestCovector φ y := by
  apply originalPiGradient_eq_on_ball hb (piSmoothH1 hφ) _
  filter_upwards [piSmoothH1_jet hφ] with x hx _ j
  exact congrArg (fun v : JetFiber => v j.succ) hx

lemma physicalSmoothCentral_jet {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    H1JetOn (piSmoothH1 hφ) centralPhysical (centralFullJetCLM s (physicalSmoothCentral s hφ).val) := by
  let f : centralSmoothFunctions := ⟨φ ∘ sourcePairCLE.symm,hφ.comp sourcePairCLE.symm.contDiff⟩
  have he : (fun y => f (sourcePairCoordinates y))=φ := by
    funext y
    exact congrArg φ (sourcePairCLE.symm_apply_apply y)
  filter_upwards [piSmoothH1_jet hφ,centralFullJetCLM_smooth_ae s f] with x hx hc hy
  change _=centralFullJetCLM s (centralEmbedL s f) x
  rw [hc hy,he,hx]

lemma physicalSmoothCentral_parent_trace {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    centralT s 0 (physicalSmoothCentral s hφ)=smoothCollarTrace s centralThickness hφ := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  change (centralSmoothTrace s ⟨φ ∘ sourcePairCLE.symm,hφ.comp sourcePairCLE.symm.contDiff⟩ 0).val 0=_
  rw [centralSmoothTrace_fst]
  ext h
  rw [centralTraceFourier_apply,smoothCollarTrace_fst]
  congr 1

lemma physicalSmoothCentral_child_trace {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (k : Fin 2) :
    centralT s k.succ (physicalSmoothCentral s hφ)=smoothCollarTrace s (-centralThickness)
      (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k))) := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  change (centralSmoothTrace s ⟨φ ∘ sourcePairCLE.symm,hφ.comp sourcePairCLE.symm.contDiff⟩ k.succ).val 0=_
  rw [centralSmoothTrace_fst]
  ext h
  rw [centralTraceFourier_apply,smoothCollarTrace_fst]
  congr 1
  funext θ
  fin_cases k <;> rfl

lemma physicalTestCovector_child {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (σ : ℝ) (y : Fin 3 → ℝ) :
    physicalTestCovector (φ ∘ sourceChildCoordinates σ) y=
      (fun i => sourceScale*physicalTestCovector φ (sourceChildCoordinates σ y) (childAxis i)) := by
  ext i
  change fderiv ℝ (φ ∘ sourceChildCoordinates σ) y (Pi.single i 1)=_
  rw [((hφ.differentiable (by simp) _).hasFDerivAt.comp y
    (sourceChildCoordinates_hasFDeriv σ y)).fderiv,ContinuousLinearMap.comp_apply]
  have he : sourceChildDerivative (Pi.single i 1)=sourceScale • Pi.single (childAxis i) 1 := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp [sourceChildDerivative_apply,childAxis]
  rw [he,map_smul]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AttachedPhysicalSmoothGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma H1JetOn.attached_gradient {s a κ : Fin 3 → ℝ} {p : centralEnergySpace s}
    {w : H1} {i : Fin 3} (hw : H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i)) :
    ∀ᵐ y : Fin 3 → ℝ,y∈physicalEndRegion i → originalPiGradient w y=
      (fun j => attachedPhysicalJet s a κ p i (WithLp.toLp 2 y) j.succ) := by
  apply originalPiGradient_eq_on_ball (fun _ => physicalEndRegion_subset_ball i) w _
  filter_upwards [hw] with x hx hy j
  exact congrArg (fun v : JetFiber => v j.succ) (hx hy)

lemma attached_child_end_energy_pullback (s a κ : Fin 3 → ℝ) (p : centralEnergySpace s)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (k : Fin 2) :
    (∫ y in physicalEndRegion k.succ,
      (fun j => attachedPhysicalJet s a κ p k.succ (WithLp.toLp 2 y) j.succ) ⬝ᵥ
        (physicalEndTensor s a k.succ y*ᵥphysicalTestCovector φ y))=
      ∫ y in sourceClosedCollarBand (-centralThickness) 0,
        fullAttachedEndGradient s (centralT s k.succ p) (a k.succ) (-centralThickness) (κ k.succ) y ⬝ᵥ
          (attachedCollarTensor s (a k.succ) y*ᵥphysicalTestCovector (φ ∘ sourceChildCoordinates (actualChildSign k)) y) := by
  have hreg : physicalEndRegion k.succ=sourceChildCoordinates (actualChildSign k) ''
      sourceClosedCollarBand (-centralThickness) 0 := by
    change (sourceChildHomeomorph (actualChildSign k)).symm ⁻¹' _=_
    ext y
    constructor
    · intro hy
      exact ⟨(sourceChildHomeomorph (actualChildSign k)).symm y,hy,
        (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y⟩
    · rintro ⟨x,hx,rfl⟩
      change (sourceChildHomeomorph (actualChildSign k)).symm
        ((sourceChildHomeomorph (actualChildSign k)) x)∈sourceClosedCollarBand (-centralThickness) 0
      simpa only [Homeomorph.symm_apply_apply] using hx
  conv_lhs => rw [hreg]
  conv_lhs => rw [sourceChild_integral (actualChildSign k) childEndBand_measurable]
  apply integral_congr_ae
  filter_upwards [] with y
  change sourceScale^3*((fun j => sourceScale⁻¹*fullAttachedEndGradient s (centralT s k.succ p)
    (a k.succ) (-centralThickness) (κ k.succ)
    ((sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)) (childAxis j)) ⬝ᵥ
    (sourceChildTensorPush k (attachedCollarTensor s (a k.succ))
      (sourceChildCoordinates (actualChildSign k) y)*ᵥphysicalTestCovector φ
        (sourceChildCoordinates (actualChildSign k) y)))=_
  have hv : (sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
  rw [hv,
    sourceChildTensorPush_mixed,physicalTestCovector_child hφ]

lemma attached_parent_jet_smooth_green (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (_ : ∀ k : Fin 2,0<a k.succ) (p : centralEnergySpace s)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)  :
    (∫ y in physicalEndRegion 0,(fun j => attachedPhysicalJet s a κ p 0 (WithLp.toLp 2 y) j.succ) ⬝ᵥ
      (physicalEndTensor s a 0 y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s 0 p))
        (spectralGraphWeight (torusRate s) (centralT s 0 (physicalSmoothCentral s hφ)))-
      κ 0*spectralGraphMean (torusRate s) (centralT s 0 (physicalSmoothCentral s hφ))+
      cylinderTerminalFlux s (κ 0) (physicalEndLength a 0) (centralT s 0 p)
        (physicalSmoothOuterTrace s hφ 0)) := by
  change (∫ y in sourceClosedCollarBand 0 centralThickness,
    fullAttachedEndGradient s (centralT s 0 p) (a 0) centralThickness (κ 0) y ⬝ᵥ
      (attachedCollarTensor s (a 0) y*ᵥphysicalTestCovector φ y))=_
  rw [fullAttachedEnd_smooth_green_neg s hs (centralT s 0 p) (κ 0) hφ ha₀
    (by norm_num [centralThickness]) (R:=physicalEndLength a 0)
    (by dsimp [physicalEndLength]; rw [abs_of_neg ha₀]; ring)
    (by norm_num) (by norm_num [centralThickness]),physicalSmoothCentral_parent_trace s hφ]
  rfl

lemma attached_child_jet_smooth_green (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (_ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) (p : centralEnergySpace s)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (k : Fin 2) :
    (∫ y in physicalEndRegion k.succ,(fun j => attachedPhysicalJet s a κ p k.succ (WithLp.toLp 2 y) j.succ) ⬝ᵥ
      (physicalEndTensor s a k.succ y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s k.succ p))
        (spectralGraphWeight (torusRate s) (centralT s k.succ (physicalSmoothCentral s hφ)))-
      κ k.succ*spectralGraphMean (torusRate s) (centralT s k.succ (physicalSmoothCentral s hφ))+
      cylinderTerminalFlux s (κ k.succ) (physicalEndLength a k.succ) (centralT s k.succ p)
        (physicalSmoothOuterTrace s hφ k.succ)) := by
  conv_lhs => rw [attached_child_end_energy_pullback s a κ p hφ k]
  rw [fullAttachedEnd_smooth_green_pos s hs (centralT s k.succ p) (κ k.succ)
    (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k))) (ha k)
    (by norm_num [centralThickness]) (R:=physicalEndLength a k.succ)
    (by dsimp [physicalEndLength]; rw [abs_of_pos (ha k)]; ring)
    (by norm_num [centralThickness]) (by norm_num),physicalSmoothCentral_child_trace s hφ k]
  rfl

lemma attached_physical_jet_smooth_green (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) (p : centralEnergySpace s)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (i : Fin 3) :
    (∫ y in physicalEndRegion i,(fun j => attachedPhysicalJet s a κ p i (WithLp.toLp 2 y) j.succ) ⬝ᵥ
      (physicalEndTensor s a i y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s i p))
        (spectralGraphWeight (torusRate s) (centralT s i (physicalSmoothCentral s hφ)))-
      κ i*spectralGraphMean (torusRate s) (centralT s i (physicalSmoothCentral s hφ))+
      cylinderTerminalFlux s (κ i) (physicalEndLength a i) (centralT s i p)
        (physicalSmoothOuterTrace s hφ i)) := by
  refine Fin.cases ?_ (fun k => ?_) i
  · exact attached_parent_jet_smooth_green s a κ hs ha₀ ha p hφ
  · exact attached_child_jet_smooth_green s a κ hs ha₀ ha p hφ k

lemma attached_physical_end_smooth_green (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) (p : centralEnergySpace s)
    (w : H1) (hw : ∀ i : Fin 3,H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i))
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (i : Fin 3) :
    (∫ y in physicalEndRegion i,originalPiGradient w y ⬝ᵥ
      (physicalEndTensor s a i y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s i p))
        (spectralGraphWeight (torusRate s) (centralT s i (physicalSmoothCentral s hφ)))-
      κ i*spectralGraphMean (torusRate s) (centralT s i (physicalSmoothCentral s hφ))+
      cylinderTerminalFlux s (κ i) (physicalEndLength a i) (centralT s i p)
        (physicalSmoothOuterTrace s hφ i)) := by
  have he : (∫ y in physicalEndRegion i,originalPiGradient w y ⬝ᵥ
      (physicalEndTensor s a i y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
    ∫ y in physicalEndRegion i,
      (fun j => attachedPhysicalJet s a κ p i (WithLp.toLp 2 y) j.succ) ⬝ᵥ
        (physicalEndTensor s a i y*ᵥphysicalTestCovector φ y) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (hw i).attached_gradient,
      ae_restrict_of_ae (piSmoothH1_gradient hφ (fun _ => physicalEndRegion_subset_ball i)),
      ae_restrict_mem (physicalEndRegion_compact i).measurableSet] with y hw hv hy
    rw [hw hy,hv hy]
  exact he.trans (attached_physical_jet_smooth_green s a κ hs ha₀ ha p hφ i)

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma attached_block_smooth_green (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) (p : centralEnergySpace s)
    (hp : ∀ v : centralEnergySpace s,
      inner ℝ (centralD s p) (centralD s v)+angularArea*
        (∑ i : Fin 3,inner ℝ (spectralGraphWeight (torusRate s) (centralT s i p))
          (spectralGraphWeight (torusRate s) (centralT s i v)))=
      angularArea*(∑ i : Fin 3,κ i*spectralGraphMean (torusRate s) (centralT s i v)))
    (w : H1) (hwc : H1JetOn w centralPhysical (centralFullJetCLM s p.val))
    (hwe : ∀ i : Fin 3,H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i))
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
      angularArea*∑ i : Fin 3,cylinderTerminalFlux s (κ i) (physicalEndLength a i)
        (centralT s i p) (physicalSmoothOuterTrace s hφ i) := by
  have han (i : Fin 3) : a i≠0 := Fin.cases ha₀.ne (fun k => (ha k).ne') i
  rw [(physicalBlockTensor_energy_sum s a hs han w (piSmoothH1 hφ)).2,
    central_physical_energy p (physicalSmoothCentral s hφ) w (piSmoothH1 hφ) hwc
      (physicalSmoothCentral_jet s hφ)]
  simp_rw [attached_physical_end_smooth_green s a κ hs ha₀ ha p w hwe hφ]
  rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hv := hp (physicalSmoothCentral s hφ)
  nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalAttachedWeakPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix UnitAddTorus

lemma smoothCollarTrace_eq_zero (s : Fin 3 → ℝ) (t : ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    (hz : ∀ θ : UnitAddTorus (Fin 2),φ (sourceAngularCollar t θ)=0) :
    smoothCollarTrace s t hφ=0 := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  ext h
  rw [smoothCollarTrace_fst]
  simp [hz,Complex.ofReal_zero,mFourierCoeff]

lemma physicalSmoothOuterTrace_compact_zero (s : Fin 3 → ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    (hφs : tsupport φ⊆(WithLp.toLp 2) ⁻¹' sourceOpenBlock) (i : Fin 3) :
    physicalSmoothOuterTrace s hφ i=0 := by
  revert i
  refine Fin.cases ?_ (fun k => ?_)
  · apply smoothCollarTrace_eq_zero
    intro θ
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hb := (sourceOpenBlock_time_iff _).mp (hφs h)
    rw [sourceAngular_time (by norm_num)] at hb
    exact (lt_irrefl 0) hb.1
  · apply smoothCollarTrace_eq_zero
    intro θ
    change φ (sourceChildCoordinates (actualChildSign k) (sourceAngularCollar 0 θ))=0
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hb := ((sourceOpenBlock_time_iff _).mp (hφs h)).2 k
    have he : (sourceChildHomeomorph (actualChildSign k)).symm
        (sourceChildCoordinates (actualChildSign k) (sourceAngularCollar 0 θ))=
        sourceAngularCollar 0 θ :=
      (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply _
    rw [he,sourceAngular_time (by norm_num)] at hb
    exact (lt_irrefl 0) hb

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_FiniteEndPhysicalH1
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

theorem compact_localLip_H1_pi {u : Coord3 → ℝ}
    (hu : ∀ x,LocalLipAt u x) {R : ℝ} (hR : R<3)
    (hs : ∀ x,R<‖WithLp.toLp 2 x‖ → u x=0) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=u (WithLp.ofLp x) ∧ ∀ i,
        weakGradient w x i=lineDeriv ℝ u (WithLp.ofLp x) (Pi.single i 1)) := by
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hh (x : R3) : LocalLipAt (u ∘ E) x :=
    (hu (E x)).comp (E.toContinuousLinearMap.lipschitz.locallyLipschitz x)
  have hz (x : R3) (hx : R<‖x‖) : (u ∘ E) x=0 := hs (E x) hx
  obtain ⟨K,hK⟩ := compact_locallyLipschitz hh (bounded_support_compact hz)
  obtain ⟨w,hw,he⟩ := compact_lipschitz_H1 hK hR hz
  refine ⟨w,hw,?_⟩
  filter_upwards [he] with x hx
  refine ⟨hx.1,fun i => (hx.2 i).trans ?_⟩
  unfold lineDeriv
  congr 1

theorem cut_physicalPeriodicField_H10 {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : ContDiff ℝ 1 f)
    {χ : Coord3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (_ : HasCompactSupport χ)
    (hs : tsupport χ⊆sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=χ (WithLp.ofLp x)*physicalPeriodicField f (WithLp.ofLp x) ∧ ∀ i,
        weakGradient w x i=lineDeriv ℝ (fun y => χ y*physicalPeriodicField f y)
          (WithLp.ofLp x) (Pi.single i 1)) := by
  refine compact_localLip_H1_pi (u:=fun y => χ y*physicalPeriodicField f y) (R:=5/2) ?_ (by norm_num) ?_
  · intro x
    by_cases hx : x∈tsupport χ
    · exact (localLipAt_of_contDiffAt (hχ.of_le (by simp)).contDiffAt).mul
        (physicalPeriodicField_localLip hp hf (sourceDirections_ne_zero_on_band (hs hx)))
    · apply (localLipAt_of_contDiffAt (contDiffAt_const (c:=(0:ℝ)))).congr
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      change χ y=0 at hy
      simp [hy]
  · intro x hx
    have hn : x∉tsupport χ := fun h => hx.not_ge (sourceBand_euclidean_bound (hs h))
    simp [image_eq_zero_of_notMem_tsupport hn]

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma flatEndCoordinates_shift (a b T : ℝ) (n : Fin 2 → ℤ) (x : Coord3) :
    flatEndCoordinates a b (x+angularShift T n)=flatEndCoordinates a b x+angularShift T n := by
  ext i
  fin_cases i <;> simp [flatEndCoordinates,angularShift]

lemma AngularPeriodic.flatEnd {E : Type*} {f : Coord3 → E} {T : ℝ}
    (hp : AngularPeriodic T f) (a b : ℝ) :
    AngularPeriodic T (fun x => f (flatEndCoordinates a b x)) := by
  intro n x
  change f (flatEndCoordinates a b (x+angularShift T n))=f (flatEndCoordinates a b x)
  rw [flatEndCoordinates_shift,hp n (flatEndCoordinates a b x)]

lemma attachedPeriodicField_zero_nhds {f : Coord3 → ℝ} {τ a b : ℝ} (hτ : 0<τ)
    (hz : ∀ x,x 0<τ → f x=0) {y : Coord3}
    (hy : a*(sourceCollarTime y-b)≤0) :
    attachedPeriodicField f a b=ᶠ[𝓝 y] (fun _ => 0) := by
  have hc : Continuous (fun y : Coord3 => a*(sourceCollarTime y-b)) :=
    continuous_const.mul (locallyLipschitz_sourceCollarTime.continuous.sub continuous_const)
  filter_upwards [(isOpen_lt hc continuous_const).mem_nhds (hy.trans_lt hτ)] with z hz'
  exact hz _ hz'

theorem attachedPeriodicCorrection_H10 {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : ContDiff ℝ 1 f)
    {τ a b l₀ l r r₀ : ℝ} (hτ : 0<τ) (hz : ∀ x,x 0<τ → f x=0)
    (hl : l₀<l) (hr : r < r₀) (hl₀ : -(1:ℝ)/100≤l₀) (hr₀ : r₀≤1/100) :
    ∃ d : H1,d∈H10 ∧
      (∀ᵐ x∂ballMeasure,a*(sourceCollarTime (WithLp.ofLp x)-b)≤0 →
        weakValue d x=0 ∧ ∀ i,weakGradient d x i=0) ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand l r →
        weakValue d x=attachedPeriodicField f a b (WithLp.ofLp x) ∧ ∀ i,
          weakGradient d x i=lineDeriv ℝ (attachedPeriodicField f a b)
            (WithLp.ofLp x) (Pi.single i 1)) := by
  obtain ⟨χ,hχ,hχc,hχb,hχs,hχ1⟩ := exists_nonneg_band_cutoff hl hr hl₀ hr₀
  have hc : ContDiff ℝ 1 (fun x => f (flatEndCoordinates a b x)) :=
    hf.comp ((contDiff_flatEndCoordinates a b).of_le (WithTop.coe_le_coe.mpr le_top))
  have hs : tsupport χ⊆sourceClosedCollarBand (-(1:ℝ)/100) (1/100) := by
    intro x hx
    exact ⟨hl₀.trans (hχs hx).1,(hχs hx).2.trans hr₀⟩
  obtain ⟨d,hd,hde⟩ := cut_physicalPeriodicField_H10 (hp.flatEnd a b) hc hχ hχc hs
  refine ⟨d,hd,?_,?_⟩
  · filter_upwards [hde] with x hx hy
    have he := attachedPeriodicField_zero_nhds hτ hz hy
    have he' : (fun y => χ y*attachedPeriodicField f a b y)=ᶠ[𝓝 (WithLp.ofLp x)]
        (fun _ => 0) := by
      filter_upwards [he] with y hy
      rw [hy,mul_zero]
    refine ⟨hx.1.trans ?_,fun i => (hx.2 i).trans ?_⟩
    · exact he'.eq_of_nhds
    · change lineDeriv ℝ (fun y => χ y*attachedPeriodicField f a b y) _ _=0
      rw [he'.lineDeriv_eq (𝕜:=ℝ)]
      simp [lineDeriv]
  · filter_upwards [hde] with x hx hy
    have he : (fun y => χ y*attachedPeriodicField f a b y)=ᶠ[𝓝 (WithLp.ofLp x)]
        attachedPeriodicField f a b := by
      filter_upwards [hχ1 _ hy] with y hy
      rw [hy,one_mul]
    exact ⟨hx.1.trans he.eq_of_nhds,fun i => (hx.2 i).trans he.lineDeriv_eq⟩

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
open Set Filter Topology MeasureTheory

lemma parentPeriodicCorrection_exists {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : ContDiff ℝ 1 f)
    {τ a : ℝ} (hτ : 0<τ) (hz : ∀ x,x 0<τ → f x=0) (ha : a<0) :
    ∃ d : H1,d∈H10 ∧ H1JetOn d centralPhysical (fun _ => 0) ∧
      H1JetOn d (physicalEndRegion 0) (periodicCorrectionJet f a 0) ∧
      ∀ k : Fin 2,H1JetOn d (physicalEndRegion k.succ) (fun _ => 0) := by
  obtain ⟨d,hd,hdz,hde⟩ := attachedPeriodicCorrection_H10 hp hf
    (a:=a) (b:=centralThickness) (l₀:= -centralThickness/2) (l:=0)
    (r:=centralThickness) (r₀:=2*centralThickness) hτ hz
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
  have hm : H1JetOn d {y | centralThickness ≤ sourceCollarTime y} (fun _ => 0) := by
    apply H1JetOn.zero_of_weak
    filter_upwards [hdz] with x hx hy
    exact hx (mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr hy))
  exact ⟨d,hd,hm.mono (fun y hy => ((centralPhysical_time_iff y).mp hy).1),
    H1JetOn.of_weak hde,fun k => hm.mono (fun y hy =>
      (show centralThickness≤2*centralThickness by norm_num [centralThickness]).trans
        (physicalChildEnd_parent_time k hy))⟩

lemma childPeriodicCorrection_exists {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : ContDiff ℝ 1 f)
    {τ a : ℝ} (hτ : 0<τ) (hz : ∀ x,x 0<τ → f x=0) (ha : 0<a) (k : Fin 2) :
    ∃ d : H1,d∈H10 ∧ H1JetOn d centralPhysical (fun _ => 0) ∧
      H1JetOn d (physicalEndRegion k.succ) (periodicCorrectionJet f a k.succ) ∧
      ∀ i : Fin 3,i≠k.succ → H1JetOn d (physicalEndRegion i) (fun _ => 0) := by
  obtain ⟨d,hd,hdz,hde⟩ := attachedPeriodicCorrection_H10 hp hf
    (a:=a) (b:= -centralThickness) (l₀:= -2*centralThickness) (l:= -centralThickness)
    (r:=0) (r₀:=centralThickness/2) hτ hz
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
  have hz' : ∀ᵐ x∂ballMeasure, WithLp.ofLp x∈{y | sourceCollarTime y≤-centralThickness} →
      weakValue d x=0 ∧ ∀ j,weakGradient d x j=0 := by
    filter_upwards [hdz] with x hx hy
    exact hx (mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr hy))
  have hm := H1JetOn.zero_of_weak
    (D:={y | sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)≤-centralThickness})
    (childH10Transport_zero_on k ⟨d,hd⟩
    {y | sourceCollarTime y≤-centralThickness} hz')
  refine ⟨childH10Transport k ⟨d,hd⟩,childH10Transport_mem_H10 k _,
    hm.mono (fun y hy => ((centralPhysical_time_iff y).mp hy).2 k),?_,?_⟩
  · exact H1JetOn.of_weak (childH10Transport_local_jet k ⟨d,hd⟩
      (D:=sourceClosedCollarBand (-centralThickness) 0)
      (fun y hy => sourceBand_mem_ball ⟨
        (show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans hy.1,
        hy.2.trans (by norm_num)⟩)
      (attachedPeriodicField f a (-centralThickness))
      (fun y j => lineDeriv ℝ (attachedPeriodicField f a (-centralThickness)) y (Pi.single j 1)) hde)
  · exact fun i hik => hm.mono (fun y hy =>
      (physicalOtherEnd_child_time k i hik hy).le.trans (by norm_num [centralThickness]))

theorem triplePeriodicCorrection_exists (f : Fin 3 → Coord3 → ℝ)
    (hp : ∀ i,AngularPeriodic (2*Real.pi) (f i)) (hf : ∀ i,ContDiff ℝ 1 (f i))
    (τ a : Fin 3 → ℝ) (hτ : ∀ i,0<τ i) (hz : ∀ i x,x 0<τ i → f i x=0)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) :
    ∃ d : H1,d∈H10 ∧ H1JetOn d centralPhysical (fun _ => 0) ∧
      ∀ i,H1JetOn d (physicalEndRegion i) (periodicCorrectionJet (f i) (a i) i) := by
  obtain ⟨dp,hdp,hpc,hpe,hpo⟩ := parentPeriodicCorrection_exists (hp 0) (hf 0) (hτ 0) (hz 0) ha₀
  have hex (k : Fin 2) := childPeriodicCorrection_exists (hp k.succ) (hf k.succ)
    (hτ k.succ) (hz k.succ) (ha k) k
  choose dc hdc hcc hce hco using hex
  refine ⟨dp+(dc 0+dc 1),H10.add_mem hdp (H10.add_mem (hdc 0) (hdc 1)),
    hpc.add_zero ((hcc 0).add_zero (hcc 1)),?_⟩
  intro i
  fin_cases i
  · exact hpe.add_zero ((hco 0 0 (by decide)).add_zero (hco 1 0 (by decide)))
  · exact (hpo 0).zero_add ((hce 0).add_zero (hco 1 1 (by decide)))
  · exact (hpo 1).zero_add ((hco 0 2 (by decide)).zero_add (hce 1))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralTerminalL2
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma spectralTerminalDensity_pair (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R)
    (f g : spectralTraceGraph (torusRate s)) :
    inner ℂ (spectralTerminalDensity s hR f) (g.val 0)=
      spectralWeightedPairL s (spectralEndWeight s R f) g := by
  change inner ℂ (spectralTerminalDensity s hR f) (g.val 0)=
    inner ℂ (spectralEndWeight s R f) (g.val 1)
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro h
  change inner ℂ (((Real.sqrt (torusRate s h)*Real.exp (-torusRate s h*R):ℝ):ℂ)*f.val 1 h)
    (g.val 0 h)=inner ℂ ((Real.exp (-torusRate s h*|R|):ℂ)*f.val 1 h) (g.val 1 h)
  rw [g.property h,abs_of_pos hR]
  simp only [RCLike.inner_apply,map_mul,Complex.conj_ofReal,Complex.ofReal_mul]
  ring

lemma terminalFluxL2CLM_trace (s : Fin 3 → ℝ) (κ : ℝ) {R : ℝ} (hR : 0<R)
    (f g : spectralTraceGraph (torusRate s)) :
    terminalFluxL2CLM s κ hR f (g.val 0)=cylinderTerminalFlux s κ R f g := by
  change κ*(g.val 0 0).re-(inner ℂ (spectralTerminalDensity s hR f) (g.val 0)).re=_
  rw [spectralTerminalDensity_pair]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalEnergyContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma physicalGradientComponent_ae {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u : H1) (i : Fin 3) :
    physicalGradientComponentCLM D i u=ᵐ[volume.restrict D] fun y => originalPiGradient u y i := by
  have he := ballWholePiJetCLM_ae_of_ae u.val (fun y => u.val (WithLp.toLp 2 y)) (by rfl)
  filter_upwards [(PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 4 => ℝ) i.succ).coeFn_compLp
      (physicalRestrictedJetCLM D u),
    lpRestrictionCLM_ae D (ballWholePiJetCLM u.val),ae_restrict_of_ae he,ae_restrict_mem hD]
    with y hp hr he hy
  change (physicalGradientComponentCLM D i u) y=_ at hp
  rw [hp]
  change (physicalRestrictedJetCLM D u) y i.succ=_
  change (physicalRestrictedJetCLM D u) y=_ at hr
  rw [hr,he,ite_eq_left (hb y hy)]
  rfl

lemma literal_matrix_energy_continuous
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ i j,AEStronglyMeasurable (fun y => A y i j) volume)
    (C : ℝ) (hC : 0≤C) (hB : ∀ y i j,|A y i j|≤C)
    {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u : H1) :
    Continuous (fun v : H1 => ∫ y in D,originalPiGradient u y ⬝ᵥ (A y*ᵥoriginalPiGradient v y)) := by
  let G := physicalGradientComponentCLM D
  let M (i j : Fin 3) := boundedMultiplier (E:=ℝ) (volume.restrict D)
    (fun y => A y i j) ((hA i j).mono_measure Measure.restrict_le_self) C hC
    (ae_of_all _ (fun y => hB y i j))
  have he (i j : Fin 3) (v : H1) :
      ((innerSL ℝ (G i u)).comp ((M i j).comp (G j))) v=
        ∫ y in D,originalPiGradient u y i*(A y i j*originalPiGradient v y j) := by
    change inner ℝ (G i u) (M i j (G j v))=_
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [physicalGradientComponent_ae hD hb u i,
      physicalGradientComponent_ae hD hb v j,
      boundedMultiplier_apply_ae (E:=ℝ) (volume.restrict D) (fun y => A y i j)
        ((hA i j).mono_measure Measure.restrict_le_self) C hC (ae_of_all _ (fun y => hB y i j))
        (G j v)] with y hu hv hm
    change G i u y=_ at hu
    change G j v y=_ at hv
    change (M i j (G j v)) y=_ at hm
    rw [hm,hu,hv]
    simp [smul_eq_mul,RCLike.inner_apply,mul_comm]
  have hi (i j : Fin 3) (v : H1) :
      Integrable (fun y => originalPiGradient u y i*(A y i j*originalPiGradient v y j)) (volume.restrict D) := by
    apply Integrable.congr (L2.integrable_inner (𝕜:=ℝ) (G i u) (M i j (G j v)))
    filter_upwards [physicalGradientComponent_ae hD hb u i,
      physicalGradientComponent_ae hD hb v j,
      boundedMultiplier_apply_ae (E:=ℝ) (volume.restrict D) (fun y => A y i j)
        ((hA i j).mono_measure Measure.restrict_le_self) C hC (ae_of_all _ (fun y => hB y i j))
        (G j v)] with y hu hv hm
    change G i u y=_ at hu
    change G j v y=_ at hv
    change (M i j (G j v)) y=_ at hm
    rw [hm,hu,hv]
    simp [smul_eq_mul,RCLike.inner_apply,mul_comm]
  have hcont : Continuous (fun v : H1 => ∑ i : Fin 3,∑ j : Fin 3,
      ((innerSL ℝ (G i u)).comp ((M i j).comp (G j))) v) := by fun_prop
  convert hcont using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  simp_rw [he]
  change (∫ y in D,∑ i : Fin 3,originalPiGradient u y i*∑ j : Fin 3,A y i j*originalPiGradient v y j)=_
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => hi i j v)
  · intro i _
    exact integrable_finsetSum _ (fun j _ => hi i j v)

lemma physicalBlockEnergy_continuous (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (u : H1) :
    Continuous (fun v : H1 => ∫ y in physicalBlockRegion,
      originalPiGradient u y ⬝ᵥ (physicalBlockTensor s a y*ᵥoriginalPiGradient v y)) := by
  obtain ⟨B,hB,hbound⟩ := (physicalBlockTensorList_properties s a hs ha
    (Finset.univ : Finset (Fin 3)).toList).2.2.2
  apply literal_matrix_energy_continuous (physicalBlockTensor s a)
    (fun i j => (physicalBlockTensor_entry_memLp s a hs ha i j).aestronglyMeasurable)
    B hB.le (fun y i j => ?_) physicalBlockRegion_compact.measurableSet
      (fun _ => physicalBlockRegion_subset_ball) u
  have hj := norm_le_pi_norm (physicalBlockTensor s a y i) j
  have hi := norm_le_pi_norm (physicalBlockTensor s a y) i
  rw [Real.norm_eq_abs] at hj
  exact hj.trans (hi.trans (hbound y))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalOuterTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_9
attribute [local instance] OAI.ScalarConductivity.instIsProbabilityMeasureUnitAddCircleVolume_solutions_9
lemma smoothOuterFourierL_apply (i : Fin 3) (φ : SmoothScalar (Fin 3 → ℝ)) (h : TorusModes) :
    smoothOuterFourierL i φ h=mFourierCoeff (fun θ => (φ.val (physicalOuterBoundary i θ):ℂ)) h := by
  change (mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ (smoothOuterContinuousL i φ)) h=_
  rw [mFourierBasis_repr,mFourierCoeff_toLp]
  rfl

lemma physicalOuterTrace_smooth (i : Fin 3) {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (s : Fin 3 → ℝ) :
    physicalOuterTraceCLM i (piSmoothH1 hφ)=(physicalSmoothOuterTrace s hφ i).val 0 := by
  have he := (dense_linear_observable_extension smoothPiH1L (smoothOuterFourierL i)
    smoothPiH1L_dense (smoothOuterFourierL_bound i)).choose_spec ⟨φ,hφ⟩
  change physicalOuterTraceCLM i (piSmoothH1 hφ)=smoothOuterFourierL i ⟨φ,hφ⟩ at he
  rw [he]
  ext h
  rw [smoothOuterFourierL_apply]
  refine Fin.cases ?_ (fun k => ?_) i
  · exact (smoothCollarTrace_fst s 0 hφ h).symm
  · exact (smoothCollarTrace_fst s 0 (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k))) h).symm

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalAttachedGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma physicalTerminalFlux_smooth (s a κ : Fin 3 → ℝ) (ha : ∀ i,a i≠0)
    (f : Fin 3 → spectralTraceGraph (torusRate s))
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    physicalTerminalFluxCLM s a κ ha f (piSmoothH1 hφ)=
      angularArea*∑ i : Fin 3,cylinderTerminalFlux s (κ i) (physicalEndLength a i)
        (f i) (physicalSmoothOuterTrace s hφ i) := by
  simp only [physicalTerminalFluxCLM,_root_.smul_apply,_root_.sum_apply,
    ContinuousLinearMap.comp_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [physicalOuterTrace_smooth i hφ s,terminalFluxL2CLM_trace]

lemma physical_block_green_extension (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (f : Fin 3 → spectralTraceGraph (torusRate s)) (w : H1)
    (hw : ∀ (φ : (Fin 3 → ℝ) → ℝ) (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ),
      (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
        (physicalBlockTensor s a y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
        angularArea*∑ i : Fin 3,cylinderTerminalFlux s (κ i) (physicalEndLength a i)
          (f i) (physicalSmoothOuterTrace s hφ i)) (v : H1) :
    (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient v y))=
      physicalTerminalFluxCLM s a κ ha f v := by
  refine smoothPiH1L_dense.induction_on v ?_ ?_
  · exact isClosed_eq (physicalBlockEnergy_continuous s a hs ha w)
      (physicalTerminalFluxCLM s a κ ha f).continuous
  intro φ
  change (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
    (physicalBlockTensor s a y*ᵥoriginalPiGradient (piSmoothH1 (smoothScalar_contDiff φ)) y))=
      physicalTerminalFluxCLM s a κ ha f (piSmoothH1 (smoothScalar_contDiff φ))
  rw [hw φ.val (smoothScalar_contDiff φ),physicalTerminalFlux_smooth]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalFiniteEndingData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma correction_initial_zero (i : Fin 3) (j : Fin 2) {x : Coord3} (hx : x 0<(z.ending i).d) :
    branchCorrection i (z.ending i) j x=0 := by
  unfold branchCorrection torusEndingCorrection axialZeroExtension
  split_ifs with h
  · linarith [(z.ending i).e_pos]
  · rfl

theorem corrected_pair_exists
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ u w : Fin 2 → H1,
      (∀ j,u j∈H10 ∧ w j∈H10) ∧
      (∀ j,H1JetOn (u j) centralPhysical (centralFullJetCLM s (z.p j).val) ∧
        H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val)) ∧
      (∀ j i,H1JetOn (u j) (physicalEndRegion i)
        (attachedPhysicalJet s z.compression (centralBasisSlopes j) (z.p j) i) ∧
        H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i)) ∧
      ∀ j v,(∫ y in physicalBlockRegion,originalPiGradient (u j) y ⬝ᵥ
        (physicalBlockTensor s z.compression y*ᵥoriginalPiGradient v y))=
        physicalTerminalFluxCLM s z.compression (centralBasisSlopes j) z.compression_ne
          (fun i => centralT s i (z.p j)) v := by
  have hu (j : Fin 2) := complete_physical_attachment s hs z.compression (centralBasisSlopes j)
    z.compression_parent z.compression_child (z.p j)
  choose u hu0 huc hue using hu
  have hd (j : Fin 2) := triplePeriodicCorrection_exists
    (fun i => branchCorrection i (z.ending i) j)
    (fun i => branchCorrection_periodic i (z.ending i) j)
    (fun i => (branchCorrection_C2 i (z.ending i) hs j).of_le (by norm_num))
    (fun i => (z.ending i).d) z.compression (fun i => (z.ending i).d_pos)
    (fun i x hx => z.correction_initial_zero i j hx) z.compression_parent z.compression_child
  choose d hd0 hdc hde using hd
  refine ⟨u,fun j => u j+d j,fun j => ⟨hu0 j,H10.add_mem (hu0 j) (hd0 j)⟩,
    fun j => ⟨huc j,(huc j).add_zero (hdc j)⟩,
    fun j i => ⟨hue j i,(hue j i).add (hde j i)⟩,?_⟩
  intro j v
  exact physical_block_green_extension s z.compression (centralBasisSlopes j) hs z.compression_ne
    (fun i => centralT s i (z.p j)) (u j)
    (fun _ hφ => attached_block_smooth_green s z.compression (centralBasisSlopes j) hs
      z.compression_parent z.compression_child (z.p j) (z.variational j) (u j) (huc j) (hue j) hφ) v

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_VariableBlockEnergy
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
open scoped Matrix.Norms.Elementwise ENNReal

attribute [local instance] OAI.ScalarConductivity.variableBlockEnergyMeasurableSpace
local instance variableBlockEnergyBorelSpace_r97ec74_1 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
lemma variableBlockTensor_entry_memLp (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0 < c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) (i j : Fin 3) :
    MemLp (fun y => variableBlockTensor K a y i j) ∞
      (volume : Measure (Fin 3 → ℝ)) := by
  have h := variableBlockTensor_properties K a hK ha
  let heval : (Matrix (Fin 3) (Fin 3) ℝ) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.proj j) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
      ((ContinuousLinearMap.proj i) : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 3 → ℝ))
  exact heval.comp_memLp' h.2.1

lemma variableBlockEnergy_continuous (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0 < c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) (u : H1) :
    Continuous (fun v : H1 => ∫ y in physicalBlockRegion,originalPiGradient u y ⬝ᵥ
      (variableBlockTensor K a y*ᵥoriginalPiGradient v y)) := by
  have h := variableBlockTensorList_properties K a hK ha (Finset.univ : Finset (Fin 3)).toList
  obtain ⟨B,hB,hbound⟩ := h.2.2.2
  apply literal_matrix_energy_continuous _ (fun i j =>
    (measurable_pi_apply j |>.comp ((measurable_pi_apply i).comp h.1)).aestronglyMeasurable)
    B hB.le (fun y i j => ?_) physicalBlockRegion_compact.measurableSet
      (fun _ => physicalBlockRegion_subset_ball) u
  exact (norm_le_pi_norm ((variableBlockTensor K a y) i) j).trans
    ((norm_le_pi_norm (variableBlockTensor K a y) i).trans (hbound y))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalSplicedGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma constantTerminalFlux_smooth (s κ : Fin 3 → ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    constantTerminalFluxCLM κ (piSmoothH1 hφ)=angularArea*∑ i : Fin 3,
      κ i*spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hφ i) := by
  simp only [constantTerminalFluxCLM,_root_.smul_apply,_root_.sum_apply,
    ContinuousLinearMap.comp_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [physicalOuterTrace_smooth i hφ s]
  rfl

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma corrected_block_green
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (w : H1) (hwc : H1JetOn w centralPhysical (centralFullJetCLM s (z.p j).val))
    (hwe : ∀ i,H1JetOn w (physicalEndRegion i) (z.correctedEndJet j i)) (v : H1) :
    (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
      (variableBlockTensor z.flatTensor z.compression y*ᵥoriginalPiGradient v y))=
      constantTerminalFluxCLM (centralBasisSlopes j) v := by
  refine smoothPiH1L_dense.induction_on v ?_ ?_
  · exact isClosed_eq (variableBlockEnergy_continuous z.flatTensor z.compression
      (z.flatTensor_properties hs) z.compression_ne w)
      (constantTerminalFluxCLM (centralBasisSlopes j)).continuous
  intro φ
  exact z.corrected_block_smooth_green hs j w hwc hwe (smoothScalar_contDiff φ)

theorem corrected_pair_green_exists
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ w : Fin 2 → H1,(∀ j,w j∈H10) ∧
      (∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val)) ∧
      (∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i)) ∧
      ∀ j v,(∫ y in physicalBlockRegion,originalPiGradient (w j) y ⬝ᵥ
        (variableBlockTensor z.flatTensor z.compression y*ᵥoriginalPiGradient v y))=
        constantTerminalFluxCLM (centralBasisSlopes j) v := by
  obtain ⟨u,w,h0,hc,he,_⟩ := z.corrected_pair_exists hs
  exact ⟨w,fun j => (h0 j).2,fun j => (hc j).2,fun j i => (he j i).2,
    fun j v => z.corrected_block_green hs j (w j) (hc j).2 (fun i => (he j i).2) v⟩

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
attribute [local instance] OAI.ScalarConductivity.physicalBlockRepresentativeMeasurableSpace
local instance physicalBlockRepresentativeBorelSpace : BorelSpace Mat3 := inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

attribute [local instance] OAI.ScalarConductivity.physicalBlockRepresentativeMeasurableSpace
lemma cartesianTensor_measurable
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    Measurable (z.cartesianTensor hs) := by
  change @Measurable Coord3 Symmetric3 _ (borel Symmetric3) (z.cartesianTensor hs)
  rw [borel_comap, ← BorelSpace.measurable_eq (α := Mat3)]
  exact ((variableBlockTensor_properties z.flatTensor z.compression (z.flatTensor_properties hs) z.compression_ne).1).subtype_mk

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalVoltageFlux
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma voltageFlux_component (v : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (y : Coord3) (i : Fin 3) (j : Fin 2) :
    voltageFlux v A y (i,j)=∑ k : Fin 3,(A y).val i k*voltageGradient v y (k,j) := rfl

lemma voltageFlux_memLp {U : Set Coord3} (v : Coord3 → Fin 2 → ℝ)
    (A : Coord3 → Symmetric3) (hE : MemLp (voltageGradient v) 2 (volume.restrict U))
    (hA : ∀ i j,MemLp (fun y => (A y).val i j) ∞ (volume.restrict U)) :
    MemLp (voltageFlux v A) 2 (volume.restrict U) := by
  apply memLp_piLp_iff.mpr
  intro ⟨i,j⟩
  simp only [voltageFlux_component]
  apply memLp_finsetSum
  intro k _
  exact ((memLp_piLp_iff.mp hE) (k,j)).mul (r := 2) (hA i k)

lemma fderiv_flux_eq_sum
    (D : Coord3 →L[ℝ] ℝ) (F : Matrix (Fin 3) (Fin 2) ℝ) (j : Fin 2) :
    D (F.col j)=∑ i : Fin 3,D (Pi.single i 1)*F i j := by
  have he : F.col j=∑ i : Fin 3,F i j • (Pi.single i 1 : Coord3) := by
    ext k
    simp [Pi.single_apply,Matrix.col_apply]
  rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,smul_eq_mul,mul_comm]

lemma smoothFluxIntegrable_of_L2 {U : Set Coord3} (v : Coord3 → Fin 2 → ℝ)
    (A : Coord3 → Symmetric3) (hF : MemLp (voltageFlux v A) 2 (volume.restrict U)) :
    SmoothFluxIntegrable volume U (conductivityFlux v A) := by
  intro j ψ hψ hc hs
  have hD (i : Fin 3) : MemLp (fun y => fderiv ℝ ψ y (Pi.single i 1)) 2 volume := by
    apply Continuous.memLp_of_hasCompactSupport
    · exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    · exact (hc.fderiv ℝ).comp_left (g:=fun D : Coord3 →L[ℝ] ℝ => D (Pi.single i 1)) rfl
  have hi : Integrable (fun y => fderiv ℝ ψ y ((conductivityFlux v A y).col j))
      (volume.restrict U) := by
    simp_rw [fderiv_flux_eq_sum]
    apply integrable_finsetSum
    intro i _
    exact ((hD i).restrict U).integrable_mul ((memLp_piLp_iff.mp hF) (i,j))
  apply (integrableOn_iff_integrable_of_support_subset (s:=U) ?_).mp hi
  intro y hy
  by_contra hn
  have hz : y∉tsupport ψ := fun h => hn (hs h)
  exact hy (by dsimp only; rw [fderiv_of_notMem_tsupport ℝ hz]; rfl)

lemma norm_elliptic_to_dot {A : Coord3 → Mat3} {c C : ℝ}
    (hc : 0 < c) (hcC : c<C)
    (hA : ∀ y (v : Coord3),c*‖v‖^2≤v ⬝ᵥ(A y*ᵥv) ∧ v ⬝ᵥ(A y*ᵥv)≤C*‖v‖^2) :
    ∃ l L : ℝ,0<l ∧ l<L ∧ ∀ y v,
      l*(v ⬝ᵥ v)≤v ⬝ᵥ(A y*ᵥv) ∧ v ⬝ᵥ(A y*ᵥv)≤L*(v ⬝ᵥ v) := by
  obtain ⟨d,D,hd,hdD,hid⟩ := identity_matrix_energy_bounds
  have hD : 0<D := hd.trans hdD
  have hC : 0<C := hc.trans hcC
  have hl : 0 < c/D := div_pos hc hD
  have hL : 0<C/d := div_pos hC hd
  have he : (c/D)*D=c := div_mul_cancel₀ _ hD.ne'
  have he' : (C/d)*d=C := div_mul_cancel₀ _ hd.ne'
  refine ⟨c/D,C/d,hl,?_,?_⟩
  · nlinarith [mul_lt_mul_of_pos_left hdD hl]
  · intro y v
    have hi := hid v
    simp only [Matrix.one_mulVec] at hi
    constructor
    · have hh := mul_le_mul_of_nonneg_left hi.2 hl.le
      calc
        _ ≤ c*‖v‖^2 := by nlinarith only [hh,he]
        _ ≤ _ := (hA y v).1
    · have hh := mul_le_mul_of_nonneg_left hi.1 hL.le
      calc
        _ ≤ C*‖v‖^2 := (hA y v).2
        _ ≤ _ := by nlinarith only [hh,he']

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_VoltageOriginalH10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

lemma voltageComponentJetCLM_ae (μ : Measure Coord3) (U : Set Coord3) (j : Fin 2)
    (z : VoltageJetSpace μ U) :
    voltageComponentJetCLM μ U j z=ᵐ[μ.restrict U]
      fun x => WithLp.toLp 2 (Fin.cases (z.1 x j) (fun i => z.2 x (i,j))) := by
  have h1 := (voltageValueComponentJet j).coeFn_compLpL (p:=2) (μ:=μ.restrict U) z.1
  have h2 := (voltageGradientComponentJet j).coeFn_compLpL (p:=2) (μ:=μ.restrict U) z.2
  have ha := Lp.coeFn_add ((voltageValueComponentJet j).compLpL 2 (μ.restrict U) z.1)
    ((voltageGradientComponentJet j).compLpL 2 (μ.restrict U) z.2)
  filter_upwards [h1,h2,ha] with x h1 h2 ha
  change (((voltageValueComponentJet j).compLpL 2 (μ.restrict U) z.1)+
    ((voltageGradientComponentJet j).compLpL 2 (μ.restrict U) z.2)) x=_
  rw [ha,Pi.add_apply,h1,h2]
  ext i
  refine Fin.cases ?_ (fun k => ?_) i <;>
    simp [voltageValueComponentJet,voltageGradientComponentJet]

lemma voltageOriginalJetCLM_ae {U : Set Coord3} (hU : MeasurableSet U) (j : Fin 2)
    (z : VoltageJetSpace volume U) :
    voltageOriginalJetCLM hU j z=ᵐ[ballMeasure] fun x =>
      if WithLp.ofLp x∈U then WithLp.toLp 2
        (Fin.cases (z.1 (WithLp.ofLp x) j) (fun i => z.2 (WithLp.ofLp x) (i,j))) else 0 := by
  have he := lpZeroExtensionCLM_ae_of_ae hU
    (voltageComponentJetCLM volume U j z) (voltageComponentJetCLM_ae volume U j z)
  have hp := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp he
  have hc := Lp.coeFn_compMeasurePreserving
    (lpZeroExtensionCLM hU (voltageComponentJetCLM volume U j z))
    (PiLp.volume_preserving_ofLp (Fin 3))
  have hr := lpRestrictionCLM_ae ball
    ((Lp.compMeasurePreservingₗᵢ ℝ
      (WithLp.ofLp : R3 → Coord3)
      (PiLp.volume_preserving_ofLp (Fin 3)))
      (lpZeroExtensionCLM hU (voltageComponentJetCLM volume U j z)))
  apply hr.trans
  apply ae_restrict_of_ae
  filter_upwards [hc,hp] with x hc hp
  apply hc.trans
  rw [hp]
  by_cases hx : WithLp.ofLp x∈U <;> simp [hx]

lemma voltage_component_smoothJet {v : Coord3 → Fin 2 → ℝ}
    (hv : Differentiable ℝ v) (j : Fin 2) (x : R3) :
    smoothJet (fun x : R3 => v (WithLp.ofLp x) j) x=
      WithLp.toLp 2 (Fin.cases (v (WithLp.ofLp x) j)
        (fun i => voltageGradient v (WithLp.ofLp x) (i,j))) := by
  ext k
  refine Fin.cases rfl (fun i => ?_) k
  change gradient (fun x : R3 => v (WithLp.ofLp x) j) x i=_
  have herr : gradient (fun x : R3 => v (WithLp.ofLp x) j) x i=
      fderiv ℝ (fun x : R3 => v (WithLp.ofLp x) j) x (EuclideanSpace.single i 1) := by
    have h : inner ℝ (EuclideanSpace.single i 1)
        (gradient (fun x : R3 => v (WithLp.ofLp x) j) x)=
        fderiv ℝ (fun x : R3 => v (WithLp.ofLp x) j) x (EuclideanSpace.single i 1) := by
      simp only [inner_gradient_right,RCLike.conj_to_real]
    simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] using h
  rw [herr]
  let P : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hd := ((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp (P x)
    (hv (P x)).hasFDerivAt).comp x P.hasFDerivAt
  have hP : (P : R3 → Coord3)=WithLp.ofLp := rfl
  rw [show fderiv ℝ (fun x : R3 => v (WithLp.ofLp x) j) x=
    (ContinuousLinearMap.proj j).comp ((fderiv ℝ v (P x)).comp P.toContinuousLinearMap) from by
      simpa only [Function.comp_def,ContinuousLinearMap.comp_assoc,ContinuousLinearMap.proj_apply,hP] using hd.fderiv]
  rfl

lemma voltageOriginalJetCLM_compact {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (j : Fin 2)
    {z : VoltageJetSpace volume U} (hz : z∈compactVoltageJets volume U) :
    voltageOriginalJetCLM hU j z∈zeroTraceAmbient := by
  obtain ⟨v,hv,hvc,hvs,hm,hg,rfl⟩ := hz
  let P : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hP : (P : R3 → Coord3)=WithLp.ofLp := rfl
  let f : R3 → ℝ := fun x => v (WithLp.ofLp x) j
  have hf : ContDiff ℝ (↑(⊤:ℕ∞)) f := by
    simpa only [Function.comp_def,hP] using
      (((contDiff_apply ℝ ℝ j).comp hv).comp P.contDiff)
  have hfc : HasCompactSupport f := by
    simpa only [Function.comp_def,show (P.toHomeomorph : R3 → Coord3)=WithLp.ofLp from rfl] using
      (hvc.comp_left (g:=fun w : Fin 2 → ℝ => w j) rfl).comp_homeomorph P.toHomeomorph
  have hfsU : tsupport f⊆(WithLp.ofLp : R3 → Coord3)⁻¹' U := by
    intro x hx
    have hs := tsupport_comp_subset_preimage (fun y : Coord3 => v y j) P.continuous
    have hm : P x∈tsupport (fun y : Coord3 => v y j) := hs hx
    exact hvs ((tsupport_comp_subset (g:=fun w : Fin 2 → ℝ => w j) rfl v) hm)
  have hfs : tsupport f⊆ball := by
    intro x hx
    simpa only [WithLp.toLp_ofLp] using hUb (WithLp.ofLp x) (hfsU hx)
  have hm' := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU).1 hm.coeFn_toLp)
  have hg' := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU).1 hg.coeFn_toLp)
  have he : voltageOriginalJetCLM hU j (hm.toLp _,hg.toLp _)=(smoothH1 f hf).val := by
    apply Lp.ext
    filter_upwards [voltageOriginalJetCLM_ae hU j (hm.toLp _,hg.toLp _),
      ae_restrict_of_ae hm',ae_restrict_of_ae hg',(smoothJet_memLp hf).coeFn_toLp]
      with x hx hm hg hfx
    change _=(smoothJet_memLp hf).toLp _ x
    rw [hfx,hx]
    by_cases hu : WithLp.ofLp x∈U
    · rw [ite_eq_left hu,hm hu,hg hu]
      exact (voltage_component_smoothJet (hv.differentiable (by simp)) j x).symm
    · rw [ite_eq_right hu]
      exact (smoothJet_zero_of_notMem_support (fun hh => hu (hfsU hh))).symm
  rw [he]
  exact smoothH1_mem_H10 f hf hfc hfs

theorem voltageOriginalJetCLM_zeroTrace {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (j : Fin 2)
    {z : VoltageJetSpace volume U} (hz : z∈zeroVoltageJets volume U) :
    voltageOriginalJetCLM hU j z∈zeroTraceAmbient := by
  exact closure_minimal
    (fun z hz => voltageOriginalJetCLM_compact hU hUb j hz)
    ((Submodule.isClosed_topologicalClosure _).preimage
      (voltageOriginalJetCLM hU j).continuous) hz

theorem voltage_original_H10_extension {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (j : Fin 2)
    {z : VoltageJetSpace volume U} (hz : z∈zeroVoltageJets volume U) :
    ∃ w : H1,w∈H10 ∧ w.val=voltageOriginalJetCLM hU j z ∧
      ∀ᵐ x∂ballMeasure,
        weakValue w x=(if WithLp.ofLp x∈U then z.1 (WithLp.ofLp x) j else 0) ∧
        ∀ i,weakGradient w x i=(if WithLp.ofLp x∈U then z.2 (WithLp.ofLp x) (i,j) else 0) := by
  have hzero := voltageOriginalJetCLM_zeroTrace hU hUb j hz
  let w : H1 := ⟨voltageOriginalJetCLM hU j z,zeroTraceAmbient_le_H1Space hzero⟩
  refine ⟨w,hzero,rfl,?_⟩
  filter_upwards [voltageOriginalJetCLM_ae hU j z] with x hx
  change w.val x=_ at hx
  by_cases hm : WithLp.ofLp x∈U
  · rw [ite_eq_left hm] at hx
    constructor
    · change w.val x 0=_
      rw [hx,ite_eq_left hm]
      rfl
    · intro i
      change (w.val x) i.succ=_
      rw [hx,ite_eq_left hm]
      rfl
  · rw [ite_eq_right hm] at hx
    constructor
    · change w.val x 0=_
      rw [hx,ite_eq_right hm]
      rfl
    · intro i
      change (w.val x) i.succ=_
      rw [hx,ite_eq_right hm]
      rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_OriginalVoltageRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

lemma originalCartesianJetCLM_ae (U : Set Coord3) (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (z : JetSpace) :
    originalCartesianJetCLM U z=ᵐ[volume.restrict U]
      fun x => z (WithLp.toLp 2 x) := by
  have he := lpZeroExtensionCLM_ae (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) z
  have hp := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp he
  have hc := Lp.coeFn_compMeasurePreserving
    (lpZeroExtensionCLM (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) z)
    (PiLp.volume_preserving_toLp (Fin 3))
  have hr := lpRestrictionCLM_ae U
    ((Lp.compMeasurePreservingₗᵢ ℝ (WithLp.toLp 2 : Coord3 → R3)
      (PiLp.volume_preserving_toLp (Fin 3)))
      (lpZeroExtensionCLM (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) z))
  apply hr.trans
  filter_upwards [ae_restrict_of_ae hc,ae_restrict_of_ae hp,ae_restrict_mem hU] with x hc hp hx
  apply hc.trans
  rw [hp]
  exact ite_eq_left (hUb x hx)

lemma originalVoltageJetCLM_ae (U : Set Coord3) (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (j : Fin 2) (z : JetSpace) :
    (originalVoltageJetCLM U j z).1=ᵐ[volume.restrict U]
        (fun x k => if k=j then z (WithLp.toLp 2 x) 0 else 0) ∧
    (originalVoltageJetCLM U j z).2=ᵐ[volume.restrict U]
        (fun x => WithLp.toLp 2 (fun ik => if ik.2=j then z (WithLp.toLp 2 x) ik.1.succ else 0)) := by
  constructor
  · have hc := (originalVoltageValue j).coeFn_compLpL (originalCartesianJetCLM U z)
    filter_upwards [hc,originalCartesianJetCLM_ae U hU hUb z] with x hx hz
    change ((originalVoltageValue j).compLpL 2 (volume.restrict U) (originalCartesianJetCLM U z)) x=_
    rw [hx,hz]
    rfl
  · have hc := (originalVoltageGradient j).coeFn_compLpL (originalCartesianJetCLM U z)
    filter_upwards [hc,originalCartesianJetCLM_ae U hU hUb z] with x hx hz
    change ((originalVoltageGradient j).compLpL 2 (volume.restrict U) (originalCartesianJetCLM U z)) x=_
    rw [hx,hz]
    rfl

lemma original_voltage_smooth_gradient (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (j : Fin 2) (x : Coord3) :
    voltageGradient (fun y : Coord3 => fun k : Fin 2 => if k=j then f (WithLp.toLp 2 y) else 0) x=
      WithLp.toLp 2 (fun ik => if ik.2=j then (smoothJet f (WithLp.toLp 2 x)) ik.1.succ else 0) := by
  let v : Coord3 → Fin 2 → ℝ := fun y k => if k=j then f (WithLp.toLp 2 y) else 0
  let P : Coord3 ≃L[ℝ] R3 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hv : ContDiff ℝ (↑(⊤:ℕ∞)) v := by
    apply contDiff_pi.mpr
    intro k
    by_cases hk : k=j
    · simpa only [v,hk,ite_true,Function.comp_def,show (P : Coord3 → R3)=WithLp.toLp 2 from rfl] using hf.comp P.contDiff
    · simpa only [v,hk,ite_false] using (contDiff_const : ContDiff ℝ (↑(⊤:ℕ∞)) (fun _ : Coord3 => (0:ℝ)))
  ext ik
  have hg := congrArg (fun w : JetFiber => w ik.1.succ)
    (voltage_component_smoothJet (hv.differentiable (by simp)) ik.2 (WithLp.toLp 2 x))
  change (voltageGradient v x).ofLp (ik.1,ik.2)=_
  by_cases hk : ik.2=j
  · have hh : (fun y : R3 => v (WithLp.ofLp y) ik.2)=f := by
      funext y
      simp [v,hk]
    rw [hh] at hg
    simpa only [WithLp.ofLp_toLp,Fin.cases_succ,WithLp.ofLp_toLp,hk,ite_true] using hg.symm
  · have hh : (fun y : R3 => v (WithLp.ofLp y) ik.2)=(fun _ => (0:ℝ)) := by
      funext y
      simp [v,hk]
    rw [hh] at hg
    simpa [smoothJet,gradient_const,hk] using hg.symm

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_OriginalH1VoltageRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

lemma original_voltage_potential_smooth (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (j : Fin 2) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Coord3 => fun k : Fin 2 => if k=j then f (WithLp.toLp 2 y) else 0) := by
  let P : Coord3 ≃L[ℝ] R3 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  apply contDiff_pi.mpr
  intro k
  by_cases hk : k=j
  · simpa only [hk,ite_true,Function.comp_def,show (P : Coord3 → R3)=WithLp.toLp 2 from rfl]
      using hf.comp P.contDiff
  · simpa only [hk,ite_false] using
      (contDiff_const : ContDiff ℝ (↑(⊤:ℕ∞)) (fun _ : Coord3 => (0:ℝ)))

lemma originalVoltageJetCLM_smooth {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (hbounded : Bornology.IsBounded U)
    (j : Fin 2) {z : JetSpace} (hz : z∈smoothJets) :
    originalVoltageJetCLM U j z∈smoothVoltageJets volume U := by
  obtain ⟨f,hf,hm,rfl⟩ := hz
  let v : Coord3 → Fin 2 → ℝ := fun y k => if k=j then f (WithLp.toLp 2 y) else 0
  have hv := original_voltage_potential_smooth f hf j
  obtain ⟨hu,hg,hh⟩ := C1_voltageJet_mem (hv.of_le (by simp)) hbounded hU
  refine ⟨v,hv,hu,hg,?_⟩
  have hm' := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).1 hm.coeFn_toLp)
  have hae := originalVoltageJetCLM_ae U hU hUb j (hm.toLp _)
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [hae.1,ae_restrict_of_ae hm',ae_restrict_mem hU,hu.coeFn_toLp]
      with x hx hm hxU hu
    rw [hx,hu]
    funext k
    rw [hm (hUb x hxU)]
    rfl
  · apply Lp.ext
    filter_upwards [hae.2,ae_restrict_of_ae hm',ae_restrict_mem hU,hg.coeFn_toLp]
      with x hx hm hxU hg
    rw [hx,hg]
    have he := original_voltage_smooth_gradient f hf j x
    rw [he]
    congr 1
    funext ik
    rw [hm (hUb x hxU)]

theorem originalVoltageJetCLM_H1 {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (hbounded : Bornology.IsBounded U)
    (j : Fin 2) (u : H1) :
    originalVoltageJetCLM U j u.val∈voltageH1Jets volume U := by
  have hs : H1Space ≤ (voltageH1Jets volume U).comap (originalVoltageJetCLM U j).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro z hz
      exact (Submodule.span ℝ (smoothVoltageJets volume U)).le_topologicalClosure
        (Submodule.subset_span (originalVoltageJetCLM_smooth hU hUb hbounded j hz))
    · exact (Submodule.isClosed_topologicalClosure _).preimage (originalVoltageJetCLM U j).continuous
  exact hs u.property

theorem scalarization_original_H1_test_bridge {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (hbounded : Bornology.IsBounded U)
    {F G : Lp FieldVector 2 (volume.restrict U)}
    (hF : ∀ W : voltageH1Jets volume U,inner ℝ W.val.2 F=inner ℝ W.val.2 G)
    (u : H1) (j : Fin 2) :
    inner ℝ (originalVoltageJetCLM U j u.val).2 F=
      inner ℝ (originalVoltageJetCLM U j u.val).2 G := by
  exact hF ⟨originalVoltageJetCLM U j u.val,originalVoltageJetCLM_H1 hU hUb hbounded j u⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_OriginalScalarizationCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

lemma originalVoltageJetCLM_pairing {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (u : H1) (j : Fin 2)
    (F : Lp FieldVector 2 (volume.restrict U)) :
    inner ℝ (originalVoltageJetCLM U j u.val).2 F=
      ∫ x,∑ i,weakGradient u (WithLp.toLp 2 x) i*F x (i,j) ∂volume.restrict U := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(originalVoltageJetCLM_ae U hU hUb j u.val).2] with x hx
  rw [hx]
  simp [PiLp.inner_apply,RCLike.inner_apply,Fintype.sum_prod_type,weakGradient,mul_comm]

theorem scalarization_original_weak_gradient_cauchy {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (hbounded : Bornology.IsBounded U)
    {F G : Lp FieldVector 2 (volume.restrict U)}
    (hF : ∀ W : voltageH1Jets volume U,inner ℝ W.val.2 F=inner ℝ W.val.2 G)
    (u : H1) (j : Fin 2) :
    (∫ x,∑ i,weakGradient u (WithLp.toLp 2 x) i*F x (i,j) ∂volume.restrict U)=
      (∫ x,∑ i,weakGradient u (WithLp.toLp 2 x) i*G x (i,j) ∂volume.restrict U) := by
  rw [←originalVoltageJetCLM_pairing hU hUb u j F,←originalVoltageJetCLM_pairing hU hUb u j G]
  exact scalarization_original_H1_test_bridge hU hUb hbounded hF u j

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_OriginalPairVoltage
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

lemma originalPairVoltageJet_H1 {U : Set Coord3} (hU : MeasurableSet U)
    (hb : ∀ y∈U,WithLp.toLp 2 y∈ball) (hbounded : Bornology.IsBounded U) (w : Fin 2 → H1) :
    originalPairVoltageJet U w∈voltageH1Jets volume U :=
  (voltageH1Jets volume U).add_mem
    (originalVoltageJetCLM_H1 hU hb hbounded 0 (w 0))
    (originalVoltageJetCLM_H1 hU hb hbounded 1 (w 1))

lemma originalPairVoltageJet_ae {U : Set Coord3} (hU : MeasurableSet U)
    (hb : ∀ y∈U,WithLp.toLp 2 y∈ball) (w : Fin 2 → H1) :
    (originalPairVoltageJet U w).1=ᵐ[volume.restrict U]
      (fun y j => weakValue (w j) (WithLp.toLp 2 y)) ∧
    (originalPairVoltageJet U w).2=ᵐ[volume.restrict U]
      (fun y => WithLp.toLp 2 (fun ij => originalPiGradient (w ij.2) y ij.1)) := by
  have h0 := originalVoltageJetCLM_ae U hU hb 0 (w 0).val
  have h1 := originalVoltageJetCLM_ae U hU hb 1 (w 1).val
  constructor
  · filter_upwards [Lp.coeFn_add (originalVoltageJetCLM U 0 (w 0).val).1
      (originalVoltageJetCLM U 1 (w 1).val).1,h0.1,h1.1] with y he h0 h1
    change ((originalVoltageJetCLM U 0 (w 0).val).1+(originalVoltageJetCLM U 1 (w 1).val).1) y=_
    rw [he,Pi.add_apply,h0,h1]
    ext j
    fin_cases j <;> simp [weakValue,jetValue] <;> rfl
  · filter_upwards [Lp.coeFn_add (originalVoltageJetCLM U 0 (w 0).val).2
      (originalVoltageJetCLM U 1 (w 1).val).2,h0.2,h1.2] with y he h0 h1
    change ((originalVoltageJetCLM U 0 (w 0).val).2+(originalVoltageJetCLM U 1 (w 1).val).2) y=_
    rw [he,Pi.add_apply,h0,h1]
    ext ⟨i,j⟩
    fin_cases j <;> simp [originalPiGradient,weakGradient]

lemma voltageGradient_component {v : Coord3 → Fin 2 → ℝ} {y : Coord3}
    (hv : DifferentiableAt ℝ v y) (i : Fin 3) (j : Fin 2) :
    (voltageGradient v y) (i,j)=fderiv ℝ (fun x => v x j) y (Pi.single i 1) := by
  have he : fderiv ℝ (fun x => v x j) y=(ContinuousLinearMap.proj j).comp (fderiv ℝ v y) :=
    ((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp y hv.hasFDerivAt).fderiv
  rw [he]
  rfl

theorem original_pair_voltageH1 {U : Set Coord3} (hU : MeasurableSet U)
    (hb : ∀ y∈U,WithLp.toLp 2 y∈ball) (hbounded : Bornology.IsBounded U)
    (w : Fin 2 → H1) (v : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (hv : ∀ᵐ y : Coord3,y∈U → v y=fun j => weakValue (w j) (WithLp.toLp 2 y))
    (hd : ∀ᵐ y : Coord3,y∈U → ∀ i : Fin 3,∀ j : Fin 2,
      fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i)
    (hr : volume (U \ regularRegion v A U)=0) :
    ∃ (hu : MemLp v 2 (volume.restrict U)) (hE : MemLp (voltageGradient v) 2 (volume.restrict U)),
      (hu.toLp _,hE.toLp _)=originalPairVoltageJet U w ∧
      (hu.toLp _,hE.toLp _)∈voltageH1Jets volume U := by
  have hp := originalPairVoltageJet_ae hU hb w
  have he : voltageGradient v=ᵐ[volume.restrict U]
      (fun y => WithLp.toLp 2 (fun ij => originalPiGradient (w ij.2) y ij.1)) := by
    filter_upwards [ae_restrict_of_ae hd,ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hr),
      ae_restrict_mem hU] with y hd hr hy
    have hyR : y∈regularRegion v A U := by simpa only [Set.mem_sdiff,hy,true_and,not_not] using hr
    ext ⟨i,j⟩
    rw [voltageGradient_component (regularRegion_differentiable hyR),hd hy i j]
    rfl
  have hv' : v=ᵐ[volume.restrict U] (originalPairVoltageJet U w).1 := by
    filter_upwards [ae_restrict_of_ae hv,ae_restrict_mem hU,hp.1] with y hv hy hp
    exact (hv hy).trans hp.symm
  have hg' := he.trans hp.2.symm
  let hu := (Lp.memLp (originalPairVoltageJet U w).1).ae_eq hv'.symm
  let hE := (Lp.memLp (originalPairVoltageJet U w).2).ae_eq hg'.symm
  have hh : (hu.toLp _,hE.toLp _)=originalPairVoltageJet U w := by
    apply Prod.ext
    · exact Lp.ext (hu.coeFn_toLp.trans hv')
    · exact Lp.ext (hE.coeFn_toLp.trans hg')
  exact ⟨hu,hE,hh,hh ▸ originalPairVoltageJet_H1 hU hb hbounded w⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalOpenVoltage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma physicalOpenBlock_subset : physicalOpenBlock⊆physicalBlockRegion := by
  rw [physicalBlockRegion_eq_closure_openBlock]
  exact subset_closure

lemma physicalOpenBlock_bounded : Bornology.IsBounded physicalOpenBlock :=
  physicalBlockRegion_compact.isBounded.subset physicalOpenBlock_subset

lemma physicalOpenBlock_subset_ball {y : Coord3} (hy : y∈physicalOpenBlock) :
    WithLp.toLp 2 y∈ball := physicalBlockRegion_subset_ball (physicalOpenBlock_subset hy)

lemma regularRegion_open_restrict {v : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U V : Set Coord3} (hV : IsOpen V) (_hVU : V⊆U) {y : Coord3}
    (hy : y∈V) (hr : y∈regularRegion v A U) : y∈regularRegion v A V := by
  obtain ⟨O,hOU,hO,hyO⟩ := mem_regularRegion_iff.mp hr
  exact mem_regularRegion_iff.mpr ⟨O∩V,inter_subset_right,hO.mono (hO.1.inter hV)
    inter_subset_left,⟨hyO,hy⟩⟩

lemma regularRegion_conull_open_restrict {v : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U V : Set Coord3} (hV : IsOpen V) (hVU : V⊆U) (hr : volume (U \ regularRegion v A U)=0) :
    volume (V \ regularRegion v A V)=0 := by
  apply measure_mono_null (t:=U \ regularRegion v A U) ?_ hr
  intro y hy
  exact ⟨hVU hy.1,fun hh => hy.2 (regularRegion_open_restrict hV hVU hy.1 hh)⟩

lemma voltageGradient_original_ae {U : Set Coord3} (hU : MeasurableSet U)
    {w : Fin 2 → H1} {v : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hd : ∀ᵐ y : Coord3,y∈U → ∀ i : Fin 3,∀ j : Fin 2,
      fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i)
    (hr : volume (U \ regularRegion v A U)=0) :
    ∀ᵐ y∂volume.restrict U,∀ i : Fin 3,∀ j : Fin 2,
      voltageGradient v y (i,j)=originalPiGradient (w j) y i := by
  filter_upwards [ae_restrict_of_ae hd,ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hr),
    ae_restrict_mem hU] with y hd hr hy i j
  have hyR : y∈regularRegion v A U := by simpa only [Set.mem_sdiff,hy,true_and,not_not] using hr
  rw [voltageGradient_component (regularRegion_differentiable hyR),hd hy i j]
  rfl

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma cartesianTensor_dot_elliptic
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ y v,
      c*(v ⬝ᵥ v)≤v ⬝ᵥ((z.cartesianTensor hs y).val*ᵥv) ∧
        v ⬝ᵥ((z.cartesianTensor hs y).val*ᵥv)≤C*(v ⬝ᵥ v) := by
  obtain ⟨c,C,hc,hcC,hb⟩ := (variableBlockTensor_properties z.flatTensor z.compression
    (z.flatTensor_properties hs) z.compression_ne).2.2.2.1
  exact norm_elliptic_to_dot hc hcC hb

lemma cartesianTensor_entry_memLp
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (U : Set Coord3) (i j : Fin 3) :
    MemLp (fun y => (z.cartesianTensor hs y).val i j) ∞ (volume.restrict U) :=
  (variableBlockTensor_entry_memLp z.flatTensor z.compression (z.flatTensor_properties hs)
    z.compression_ne i j).restrict U

lemma corrected_voltage_divergence
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (w : Fin 2 → H1)
    (hc : ∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val))
    (he : ∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i))
    (v : Coord3 → Fin 2 → ℝ)
    (hd : ∀ᵐ y∂volume.restrict physicalOpenBlock,∀ i : Fin 3,∀ j : Fin 2,
      voltageGradient v y (i,j)=originalPiGradient (w j) y i)
    (j : Fin 2) {ψ : Coord3 → ℝ} (hψ : ContDiff ℝ (↑(⊤:ℕ∞)) ψ)
    (hψs : tsupport ψ⊆physicalOpenBlock) :
    (∫ y,fderiv ℝ ψ y ((conductivityFlux v (z.cartesianTensor hs) y).col j))=0 := by
  have hzero : ∀ y∉physicalOpenBlock,fderiv ℝ ψ y ((conductivityFlux v (z.cartesianTensor hs) y).col j)=0 := by
    intro y hy
    rw [fderiv_of_notMem_tsupport ℝ (fun hh => hy (hψs hh))]
    rfl
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hg := z.corrected_block_smooth_green hs j (w j) (hc j) (he j) hψ
  rw [constantTerminalFlux_smooth s,show (∑ i : Fin 3,centralBasisSlopes j i*
    spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hψ i))=0 from by
      simp only [physicalSmoothOuterTrace_compact_zero s hψ hψs,spectralGraphMean,map_zero,mul_zero,
        Finset.sum_const_zero],mul_zero] at hg
  rw [physicalBlockRegion_openBlock_restrict] at hg
  refine (integral_congr_ae ?_).trans hg
  filter_upwards [hd,ae_restrict_of_ae (piSmoothH1_gradient hψ
    (fun _ => physicalOpenBlock_subset_ball)),ae_restrict_mem physicalOpenBlock_open.measurableSet]
    with y hd hp hy
  rw [hp hy,fderiv_flux_eq_sum]
  change (∑ i : Fin 3,fderiv ℝ ψ y (Pi.single i 1)*voltageFlux v (z.cartesianTensor hs) y (i,j))=_
  simp_rw [voltageFlux_component,hd]
  change physicalTestCovector ψ y ⬝ᵥ
    ((z.cartesianTensor hs y).val*ᵥoriginalPiGradient (w j) y)=_
  have hsym : (z.cartesianTensor hs y).valᵀ=(z.cartesianTensor hs y).val :=
    (z.cartesianTensor hs y).property
  have hh := Matrix.dotProduct_transpose_mulVec (z.cartesianTensor hs y).val
    (physicalTestCovector ψ y) (originalPiGradient (w j) y)
  rw [hsym] at hh
  exact hh

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma ae_original_to_cartesian {P : R3 → Prop} (hP : ∀ᵐ x∂ballMeasure,P x) :
    ∀ᵐ y : Coord3,WithLp.toLp 2 y∈ball → P (WithLp.toLp 2 y) :=
  (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).mp hP)

theorem original_pair_zeroVoltage_extension {U : Set Coord3} (hU : MeasurableSet U)
    (hb : ∀ y∈U,WithLp.toLp 2 y∈ball) (w : Fin 2 → H1) (hw : ∀ j,w j∈H10)
    (Z : VoltageJetSpace volume U)
    (hz : Z-originalPairVoltageJet U w∈zeroVoltageJets volume U) :
    ∃ q : Fin 2 → H1,(∀ j,q j∈H10) ∧
      (∀ j,(q j-w j).val=voltageOriginalJetCLM hU j (Z-originalPairVoltageJet U w)) ∧
      (∀ᵐ y∂volume.restrict U,Z.1 y=fun j => weakValue (q j) (WithLp.toLp 2 y)) ∧
      (∀ᵐ y∂volume.restrict U,∀ i : Fin 3,∀ j : Fin 2,
        Z.2 y (i,j)=originalPiGradient (q j) y i) := by
  have hd (j : Fin 2) := voltage_original_H10_extension hU hb j hz
  choose d hd hdv hdae using hd
  refine ⟨fun j => w j+d j,fun j => H10.add_mem (hw j) (hd j),fun j => ?_,?_,?_⟩
  · rw [add_sub_cancel_left]
    exact hdv j
  · have he := originalPairVoltageJet_ae hU hb w
    filter_upwards [he.1,ae_restrict_of_ae (ae_original_to_cartesian (ae_all_iff.mpr hdae)),
      ae_restrict_of_ae (ae_original_to_cartesian (ae_all_iff.mpr (fun j => weakValue_add (w j) (d j)))),
      Lp.coeFn_sub Z.1 (originalPairVoltageJet U w).1,ae_restrict_mem hU] with y he hd ha hz hy
    ext j
    rw [ha (hb y hy) j]
    change _=weakValue (w j) (WithLp.toLp 2 y)+weakValue (d j) (WithLp.toLp 2 y)
    have hv := (hd (hb y hy) j).1
    simp only [ite_eq_left hy] at hv
    rw [hv]
    change _=weakValue (w j) (WithLp.toLp 2 y)+
      ((Z.1-(originalPairVoltageJet U w).1) y) j
    rw [hz,Pi.sub_apply,he]
    simp
  · have he := originalPairVoltageJet_ae hU hb w
    filter_upwards [he.2,ae_restrict_of_ae (ae_original_to_cartesian (ae_all_iff.mpr hdae)),
      ae_restrict_of_ae (ae_original_to_cartesian (ae_all_iff.mpr (fun j => weakGradient_add (w j) (d j)))),
      Lp.coeFn_sub Z.2 (originalPairVoltageJet U w).2,ae_restrict_mem hU] with y he hd ha hz hy i j
    change _=weakGradient (w j+d j) (WithLp.toLp 2 y) i
    rw [ha (hb y hy) j]
    change _=weakGradient (w j) (WithLp.toLp 2 y) i+weakGradient (d j) (WithLp.toLp 2 y) i
    have hv := (hd (hb y hy) j).2 i
    simp only [ite_eq_left hy] at hv
    rw [hv]
    change _=weakGradient (w j) (WithLp.toLp 2 y) i+
      ((Z.2-(originalPairVoltageJet U w).2) y) (i,j)
    rw [hz,Pi.sub_apply,he]
    change _=originalPiGradient (w j) y i+(Z.2 y (i,j)-originalPiGradient (w j) y i)
    ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_PhysicalScalarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

theorem scalar_pair_green_exists_oai
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ (σ : Coord3 → ℝ) (c C : ℝ) (w q : Fin 2 → H1),
      Measurable σ ∧ MemLp σ ∞ (volume.restrict physicalOpenBlock) ∧
      0 < c ∧ c<C ∧ (∀ᵐ y∂volume.restrict physicalOpenBlock,σ y∈Icc c C) ∧
      (∀ j,q j∈H10) ∧
      (∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val)) ∧
      (∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i)) ∧
      (∃ Z : VoltageJetSpace volume physicalOpenBlock,
        Z-originalPairVoltageJet physicalOpenBlock w∈zeroVoltageJets volume physicalOpenBlock ∧
        ∀ j,(q j-w j).val=voltageOriginalJetCLM physicalOpenBlock_open.measurableSet j
          (Z-originalPairVoltageJet physicalOpenBlock w)) ∧
      ∀ j (h : H1),(∫ y in physicalOpenBlock,σ y*(originalPiGradient (q j) y ⬝ᵥ
        originalPiGradient h y))=constantTerminalFluxCLM (centralBasisSlopes j) h := by
  let : IsFiniteMeasure (volume.restrict physicalOpenBlock) :=
    isFiniteMeasure_restrict.mpr physicalOpenBlock_bounded.measure_lt_top.ne
  let : Fact ((2:ℝ≥0∞)≠∞) := ⟨by norm_num⟩
  obtain ⟨w,hw,hc,he,hgreen⟩ := z.corrected_pair_green_exists hs
  obtain ⟨v,hv,hd,hr⟩ := z.corrected_pair_representative hs w hc he
  have hv' : ∀ᵐ y : Coord3,y∈physicalOpenBlock → v y=fun j => weakValue (w j) (WithLp.toLp 2 y) := by
    filter_upwards [hv] with y hy hyU
    exact hy (physicalOpenBlock_subset hyU)
  have hd' : ∀ᵐ y : Coord3,y∈physicalOpenBlock → ∀ i : Fin 3,∀ j : Fin 2,
      fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i := by
    filter_upwards [hd] with y hy hyU
    exact hy (physicalOpenBlock_subset hyU)
  have hr' := regularRegion_conull_open_restrict physicalOpenBlock_open physicalOpenBlock_subset hr
  obtain ⟨hu,hE,hjet,hH1⟩ := original_pair_voltageH1 physicalOpenBlock_open.measurableSet
    (fun _ => physicalOpenBlock_subset_ball) physicalOpenBlock_bounded w v (z.cartesianTensor hs) hv' hd' hr'
  have hg := voltageGradient_original_ae physicalOpenBlock_open.measurableSet hd' hr'
  have hF := voltageFlux_memLp v (z.cartesianTensor hs) hE
    (z.cartesianTensor_entry_memLp hs physicalOpenBlock)
  obtain ⟨l,L,hl,hlL,hb⟩ := z.cartesianTensor_dot_elliptic hs
  obtain ⟨Z,F,σ,hσm,hσL,hzero,hσ,hcau,_⟩ := finite_field_scalarization volume hl hlL.le
    physicalOpenBlock_bounded physicalOpenBlock_open.measurableSet v (z.cartesianTensor hs)
    (z.cartesianTensor_measurable hs) hu hE hF hH1 (smoothFluxIntegrable_of_L2 v _ hF)
    (fun j ψ hψ _ hψs => z.corrected_voltage_divergence hs w hc he v hg j hψ hψs)
    hr' (Filter.Eventually.of_forall (fun y _ => hb y))
  rw [hjet] at hzero
  obtain ⟨q,hq,hqjet,hqv,hqg⟩ := original_pair_zeroVoltage_extension physicalOpenBlock_open.measurableSet
    (fun _ => physicalOpenBlock_subset_ball) w hw Z.val hzero
  refine ⟨σ,laminateLower l L,laminateUpper L,w,q,hσm,hσL,
    (uniform_laminate_coverage hl hlL.le).1,(uniform_laminate_coverage hl hlL.le).2.1,
    hσ.mono (fun _ h => h.1),hq,hc,he,⟨Z.val,hzero,hqjet⟩,?_⟩
  intro j h
  have hcc := scalarization_original_weak_gradient_cauchy physicalOpenBlock_open.measurableSet
    (fun _ => physicalOpenBlock_subset_ball) physicalOpenBlock_bounded hcau h j
  have hlhs : (∫ y,∑ i,weakGradient h (WithLp.toLp 2 y) i*F y (i,j) ∂volume.restrict physicalOpenBlock)=
      ∫ y in physicalOpenBlock,σ y*(originalPiGradient (q j) y ⬝ᵥ originalPiGradient h y) := by
    apply integral_congr_ae
    filter_upwards [hσ,hqg] with y hσ hqg
    rw [hσ.2]
    simp only [PiLp.smul_apply,smul_eq_mul,hqg,dotProduct,Finset.mul_sum,originalPiGradient]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrhs : (∫ y,∑ i,weakGradient h (WithLp.toLp 2 y) i*(hF.toLp _) y (i,j) ∂volume.restrict physicalOpenBlock)=
      ∫ y in physicalOpenBlock,originalPiGradient (w j) y ⬝ᵥ
        (variableBlockTensor z.flatTensor z.compression y*ᵥoriginalPiGradient h y) := by
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp,hg] with y hF hg
    rw [hF]
    simp_rw [voltageFlux_component,hg]
    change originalPiGradient h y ⬝ᵥ((z.cartesianTensor hs y).val*ᵥoriginalPiGradient (w j) y)=_
    have hsym : (z.cartesianTensor hs y).valᵀ=(z.cartesianTensor hs y).val := (z.cartesianTensor hs y).property
    have hh := Matrix.dotProduct_transpose_mulVec (z.cartesianTensor hs y).val
      (originalPiGradient h y) (originalPiGradient (w j) y)
    rw [hsym] at hh
    exact hh
  rw [hlhs,hrhs] at hcc
  exact hcc.trans (by simpa only [physicalOpenBlock,physicalBlockRegion_openBlock_restrict] using hgreen j h)

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists_oai := @OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists_oai
