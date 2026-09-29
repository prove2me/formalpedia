-- Prove2me | solution 1 for NumberField.InfiniteAdeleRing.exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cef79b2e-a0af-5219-8272-2cc85596e121

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

set_option linter.unusedSectionVars false

noncomputable section

namespace ArchBorelCoord

open AutomorphicForm Topology

variable (K : Type) [Field K] [NumberField K]

scoped instance secondCountable_completion (w : InfinitePlace K) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance secondCountable_Koo : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace K) → w.Completion))

scoped instance secondCountable_units : SecondCountableTopology (InfiniteAdeleRing K)ˣ := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompact_units : LocallyCompactSpace (InfiniteAdeleRing K)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance secondCountable_GL : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompact_GL : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

abbrev Bgrp : Subgroup (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.borelSubgroup (InfiniteAdeleRing K)

theorem isClosed_B : IsClosed (Bgrp K : Set (GL (Fin 2) (InfiniteAdeleRing K))) := by
  have : (Bgrp K : Set (GL (Fin 2) (InfiniteAdeleRing K))) =
      (fun g : GL (Fin 2) (InfiniteAdeleRing K) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0) ⁻¹' {0} := by
    ext g; exact mem_borelSubgroup_iff _
  rw [this]
  exact isClosed_singleton.preimage ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))).matrix_elem 1 0)

scoped instance secondCountable_B : SecondCountableTopology (Bgrp K) := TopologicalSpace.Subtype.secondCountableTopology _
scoped instance locallyCompact_B : LocallyCompactSpace (Bgrp K) := (isClosed_B K).locallyCompactSpace
scoped instance measurableSpace_B : MeasurableSpace (Bgrp K) := borel _
scoped instance borelSpace_B : BorelSpace (Bgrp K) := ⟨rfl⟩
scoped instance measurableSpace_GL : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf _
scoped instance borelSpace_GL : BorelSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf _

theorem continuous_unipotentGL2 :
    Continuous (fun y : InfiniteAdeleRing K => (unipotentGL2 y : GL (Fin 2) (InfiniteAdeleRing K))) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Function.comp_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : ∀ y : InfiniteAdeleRing K, (↑((unipotentGL2 y : GL (Fin 2) (InfiniteAdeleRing K))⁻¹) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) = !![1, -y; 0, 1] := fun y => rfl
    simp_rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_scalar :
    Continuous (Matrix.GeneralLinearGroup.scalar (Fin 2) : (InfiniteAdeleRing K)ˣ → GL (Fin 2) (InfiniteAdeleRing K)) := by
  have hval : Continuous fun u : (InfiniteAdeleRing K)ˣ =>
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
    change Continuous fun u : (InfiniteAdeleRing K)ˣ => Matrix.scalar (Fin 2) (u : InfiniteAdeleRing K)
    simp_rw [Matrix.scalar_apply]
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp_rw [← map_inv]
  exact hval.comp continuous_inv

theorem diagUnits2_one_val (t : (InfiniteAdeleRing K)ˣ) :
    ((diagUnits2 t 1 : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
      Matrix.diagonal ![(t : InfiniteAdeleRing K), 1] := by
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem continuous_diag :
    Continuous (fun t : (InfiniteAdeleRing K)ˣ => (diagUnits2 t 1 : GL (Fin 2) (InfiniteAdeleRing K))) := by
  have hval : Continuous fun t : (InfiniteAdeleRing K)ˣ =>
      ((diagUnits2 t 1 : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
    simp_rw [diagUnits2_one_val]
    refine (continuous_pi fun i => ?_).matrix_diagonal
    fin_cases i
    · exact Units.continuous_val
    · exact continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have : ∀ t : (InfiniteAdeleRing K)ˣ, (diagUnits2 t 1 : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ = diagUnits2 t⁻¹ 1 := by
    intro t
    rw [inv_eq_iff_mul_eq_one]
    apply Units.ext
    rw [Units.val_mul, diagUnits2_one_val, diagUnits2_one_val, Matrix.diagonal_mul_diagonal, Units.val_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  simp_rw [this]
  exact hval.comp continuous_inv

def psiG (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K) : GL (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) p.1 * diagUnits2 p.2.1 1 * unipotentGL2 p.2.2

theorem psiG_apply (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K) (i j : Fin 2) :
    ((psiG K p : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j =
      !![(p.1 : InfiniteAdeleRing K) * p.2.1, (p.1 : InfiniteAdeleRing K) * p.2.1 * p.2.2;
         0, (p.1 : InfiniteAdeleRing K)] i j := by
  rw [psiG, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe, diagUnits2_one_val]
  change (Matrix.scalar (Fin 2) (p.1 : InfiniteAdeleRing K) * Matrix.diagonal ![(p.2.1 : InfiniteAdeleRing K), 1] *
    !![1, p.2.2; 0, 1]) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem psiG_mem (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K) :
    psiG K p ∈ Bgrp K := by
  rw [Bgrp, mem_borelSubgroup_iff, psiG_apply]; rfl

theorem continuous_psiG : Continuous (psiG K) :=
  (((continuous_scalar K).comp continuous_fst).mul
    ((continuous_diag K).comp (continuous_fst.comp continuous_snd))).mul
    ((continuous_unipotentGL2 K).comp (continuous_snd.comp continuous_snd))

def psi (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K) : Bgrp K :=
  ⟨psiG K p, psiG_mem K p⟩

theorem continuous_psi : Continuous (psi K) := (continuous_psiG K).subtype_mk _

def theta (b : Bgrp K) : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K :=
  (borelDiagSnd b, borelDiagFst b * (borelDiagSnd b)⁻¹,
    (((borelDiagFst b)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) *
      ((b : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1)

theorem continuous_entry (i j : Fin 2) : Continuous fun b : Bgrp K =>
    (((b : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) :=
  ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))).matrix_elem i j).comp continuous_subtype_val

theorem continuous_borelDiagSnd : Continuous (borelDiagSnd : Bgrp K → (InfiniteAdeleRing K)ˣ) := by
  refine Units.continuous_iff.mpr ⟨continuous_entry K 1 1, ?_⟩
  simp_rw [← map_inv]
  exact (continuous_entry K 1 1).comp continuous_inv

theorem continuous_borelDiagFst : Continuous (borelDiagFst : Bgrp K → (InfiniteAdeleRing K)ˣ) := by
  refine Units.continuous_iff.mpr ⟨continuous_entry K 0 0, ?_⟩
  simp_rw [← map_inv]
  exact (continuous_entry K 0 0).comp continuous_inv

theorem continuous_theta : Continuous (theta K) := by
  refine (continuous_borelDiagSnd K).prodMk (((continuous_borelDiagFst K).mul (continuous_borelDiagSnd K).inv).prodMk
    ((Units.continuous_val.comp (continuous_borelDiagFst K).inv).mul (continuous_entry K 0 1)))

theorem theta_psi (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K) : theta K (psi K p) = p := by
  obtain ⟨u, t, x⟩ := p
  have hsnd : borelDiagSnd (psi K (u, t, x)) = u := Units.ext (by
    change ((psiG K (u, t, x) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 =
      (u : InfiniteAdeleRing K)
    rw [psiG_apply]; rfl)
  have hfst : borelDiagFst (psi K (u, t, x)) = u * t := Units.ext (by
    change ((psiG K (u, t, x) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 =
      ((u * t : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
    rw [psiG_apply, Units.val_mul]; rfl)
  have h01 : (((psi K (u, t, x) : Bgrp K) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 =
      (u : InfiniteAdeleRing K) * t * x := by
    change ((psiG K (u, t, x) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = _
    rw [psiG_apply]; rfl
  simp only [theta, hsnd, hfst, h01]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show u * t * u⁻¹ = t
    rw [mul_comm u t, mul_assoc, mul_inv_cancel, mul_one]
  · show (((u * t)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * ((u : InfiniteAdeleRing K) * t * x) = x
    rw [← Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]

theorem psi_theta (b : Bgrp K) : psi K (theta K b) = b := by
  have h10 : (((b : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0) = 0 :=
    (mem_borelSubgroup_iff _).mp b.2
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change ((psiG K (theta K b) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j = _
  rw [psiG_apply]
  set M := (((b : GL (Fin 2) (InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) with hM
  have hu : ((borelDiagSnd b : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = M 1 1 := rfl
  have ht : ((borelDiagFst b : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = M 0 0 := rfl
  have hinvS : M 1 1 * (((borelDiagSnd b)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1 := by rw [← hu, Units.mul_inv]
  have hinvF : M 0 0 * (((borelDiagFst b)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1 := by rw [← ht, Units.mul_inv]
  have e00 : ((borelDiagSnd b : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) *
      ((borelDiagFst b * (borelDiagSnd b)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = M 0 0 := by
    rw [Units.val_mul, hu, ht, mul_left_comm, hinvS, mul_one]
  have e01 : ((borelDiagSnd b : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) *
      ((borelDiagFst b * (borelDiagSnd b)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) *
      ((((borelDiagFst b)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * M 0 1) = M 0 1 := by
    rw [e00, ← mul_assoc, hinvF, one_mul]
  simp only [theta]
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact h10.symm
  · exact hu

def psiHomeo : ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K) ≃ₜ Bgrp K where
  toFun := psi K
  invFun := theta K
  left_inv := theta_psi K
  right_inv := psi_theta K
  continuous_toFun := continuous_psi K
  continuous_invFun := continuous_theta K

def lmul (p q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K) :
    (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K :=
  (p.1 * q.1, p.2.1 * q.2.1, q.2.2 + ((q.2.1⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * p.2.2)

theorem psi_mul (p q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K) :
    psi K p * psi K q = psi K (lmul K p q) := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change (((psiG K p : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) *
      ((psiG K q : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) i j =
    ((psiG K (lmul K p q) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, psiG_apply, psiG_apply, psiG_apply, psiG_apply, psiG_apply]
  have hq : (q.2.1 : InfiniteAdeleRing K) * ((q.2.1⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1 := Units.mul_inv _
  simp only [lmul, Units.val_mul]
  fin_cases i <;> fin_cases j
  · simp; ring
  · simp
    linear_combination (-((p.1 : InfiniteAdeleRing K) * p.2.1 * q.1 * p.2.2)) * hq
  · simp
  · simp

variable [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
  (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
  [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
  (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]

def rho : Measure ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K) :=
  ρ.prod (ρ.prod lam)

def kappa : Measure (Bgrp K) := (rho K lam ρ).map (psi K)

scoped instance sigmaFinite_lam : SigmaFinite lam := by infer_instance
scoped instance sigmaFinite_ρ : SigmaFinite ρ := by infer_instance
scoped instance sFinite_rho : SFinite (rho K lam ρ) := by unfold rho; infer_instance

theorem measurePreserving_skew (t₀ : (InfiniteAdeleRing K)ˣ) (x₀ : InfiniteAdeleRing K) :
    MeasurePreserving (fun q : (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K =>
        (t₀ * q.1, q.2 + ((q.1⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * x₀)) (ρ.prod lam) (ρ.prod lam) := by
  refine (measurePreserving_mul_left ρ t₀).skew_product (g := fun t x => x + ((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * x₀)
    ?_ ?_
  · exact measurable_snd.add ((Units.continuous_val.comp continuous_inv).measurable.comp measurable_fst |>.mul measurable_const)
  · exact Filter.Eventually.of_forall fun t => map_add_right_eq_self lam _

theorem map_lmul_rho (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K) :
    (rho K lam ρ).map (lmul K p) = rho K lam ρ := by
  obtain ⟨u₀, t₀, x₀⟩ := p
  have hl : lmul K (u₀, t₀, x₀) = Prod.map (fun u => u₀ * u)
      (fun q : (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K =>
        (t₀ * q.1, q.2 + ((q.1⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * x₀)) := rfl
  rw [hl, rho]
  exact ((measurePreserving_mul_left ρ u₀).prod (measurePreserving_skew K lam ρ t₀ x₀)).map_eq

theorem continuous_lmul (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K) : Continuous (lmul K p) := by
  unfold lmul
  exact (continuous_const.mul continuous_fst).prodMk
    ((continuous_const.mul (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_snd.comp continuous_snd).add
        ((Units.continuous_val.comp ((continuous_fst.comp continuous_snd).inv)).mul continuous_const)))

scoped instance isMulLeftInvariant_kappa : (kappa K lam ρ).IsMulLeftInvariant := by
  refine ⟨fun b₀ => ?_⟩
  obtain ⟨p₀, rfl⟩ : ∃ p₀, psi K p₀ = b₀ := ⟨theta K b₀, psi_theta K b₀⟩
  rw [kappa, Measure.map_map (measurable_const_mul _) (continuous_psi K).measurable]
  have : (fun b => psi K p₀ * b) ∘ psi K = psi K ∘ lmul K p₀ := funext fun q => psi_mul K p₀ q
  rw [this, ← Measure.map_map (continuous_psi K).measurable, map_lmul_rho]
  exact (continuous_lmul K p₀).measurable

scoped instance isFiniteMeasureOnCompacts_rho : IsFiniteMeasureOnCompacts (rho K lam ρ) := by
  unfold rho; infer_instance

scoped instance isFiniteMeasureOnCompacts_kappa : IsFiniteMeasureOnCompacts (kappa K lam ρ) := by
  refine ⟨fun C hC => ?_⟩
  rw [kappa, Measure.map_apply (continuous_psi K).measurable hC.measurableSet]
  exact ((psiHomeo K).isCompact_preimage.mpr hC).measure_lt_top

theorem kappa_univ_ne_zero : kappa K lam ρ Set.univ ≠ 0 := by
  rw [kappa, Measure.map_apply (continuous_psi K).measurable MeasurableSet.univ, Set.preimage_univ, rho,
    ← Set.univ_prod_univ, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod]
  exact mul_ne_zero (isOpen_univ.measure_ne_zero _ Set.univ_nonempty)
    (mul_ne_zero (isOpen_univ.measure_ne_zero _ Set.univ_nonempty) (isOpen_univ.measure_ne_zero _ Set.univ_nonempty))

theorem exists_eq_mul_lintegral_kappa (μB : Measure (Bgrp K)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ F : Bgrp K → ℝ≥0∞,
      ∫⁻ b, F b ∂μB = c * ∫⁻ b, F b ∂(kappa K lam ρ) := by
  set c' := Measure.haarScalarFactor (kappa K lam ρ) μB with hc'
  have hκ : kappa K lam ρ = c' • μB := Measure.isMulLeftInvariant_eq_smul (kappa K lam ρ) μB
  have hc0 : c' ≠ 0 := by
    intro h0
    apply kappa_univ_ne_zero K lam ρ
    rw [hκ, h0, zero_smul, Measure.coe_zero, Pi.zero_apply]
  refine ⟨((c' : ℝ≥0∞))⁻¹, ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top, ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hc0),
    fun F => ?_⟩
  have h1 : ∫⁻ b, F b ∂(kappa K lam ρ) = (c' : ℝ≥0∞) * ∫⁻ b, F b ∂μB := by
    rw [hκ, lintegral_smul_measure]
    rfl
  rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hc0) ENNReal.coe_ne_top, one_mul]

theorem main (μB : Measure (Bgrp K)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ F : GL (Fin 2) (InfiniteAdeleRing K) → ℝ≥0∞, Measurable F →
        ∫⁻ b, F (b : GL (Fin 2) (InfiniteAdeleRing K)) ∂μB =
          c * ∫⁻ u, ∫⁻ t, ∫⁻ x,
                F (Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagUnits2 t 1 * AutomorphicForm.unipotentGL2 x)
              ∂lam ∂ρ ∂ρ := by
  obtain ⟨c, hc0, hctop, hc⟩ := exists_eq_mul_lintegral_kappa K lam ρ μB
  refine ⟨c, hc0, hctop, fun F hF => ?_⟩
  rw [hc (fun b => F b)]
  congr 1
  set Φ : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K → ℝ≥0∞ := fun p => F (psiG K p) with hΦ_def
  have hΦ : Measurable Φ := hF.comp (continuous_psiG K).measurable
  have hFb : Measurable fun b : Bgrp K => F (b : GL (Fin 2) (InfiniteAdeleRing K)) := hF.comp continuous_subtype_val.measurable
  rw [kappa, lintegral_map hFb (continuous_psi K).measurable]
  change ∫⁻ p, Φ p ∂(rho K lam ρ) = _
  rw [rho, lintegral_prod _ hΦ.aemeasurable]
  refine lintegral_congr fun u => ?_
  have hΦu : Measurable fun q : (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K => Φ (u, q) := hΦ.comp measurable_prodMk_left
  rw [lintegral_prod _ hΦu.aemeasurable]
  rfl

end ArchBorelCoord
p2m_reactivate "P2MW.S_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2.ArchBorelCoord"

end
p2m_reactivate "P2MW.S_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2.ArchBorelCoord"

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (μB : @Measure ↥(AutomorphicForm.borelSubgroup (InfiniteAdeleRing K)) (borel _))
    (hμB : @Measure.IsHaarMeasure _ _ _ (borel _) μB) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ F : GL (Fin 2) (InfiniteAdeleRing K) → ℝ≥0∞, Measurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] F →
        @lintegral _ (borel _) μB (fun b => F (b : GL (Fin 2) (InfiniteAdeleRing K))) =
          c * ∫⁻ u, ∫⁻ t, ∫⁻ x,
                F (Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagUnits2 t 1 * AutomorphicForm.unipotentGL2 x)
              ∂lam ∂ρ ∂ρ := by
  letI : MeasurableSpace ↥(AutomorphicForm.borelSubgroup (InfiniteAdeleRing K)) := borel _
  haveI : BorelSpace ↥(AutomorphicForm.borelSubgroup (InfiniteAdeleRing K)) := ⟨rfl⟩
  haveI : μB.IsHaarMeasure := hμB
  exact ArchBorelCoord.main K lam ρ μB

end S_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2
end P2MW
export P2MW.S_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2 (solution)
