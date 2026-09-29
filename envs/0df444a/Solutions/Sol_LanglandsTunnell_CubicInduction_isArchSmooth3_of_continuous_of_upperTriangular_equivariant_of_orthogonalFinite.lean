-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/01899eb5-5561-5039-8308-385f50f4c123

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Theorems.Thm_LanglandsTunnell_CubicInduction_archRealLift3_mul_eq_mul_archRealLift3_conj
import Theorems.Thm_LanglandsTunnell_CubicInduction_componentAt3_archRealLift3_eq_one_and_realMat_archComponent3_eq
import Theorems.Thm_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates
import Theorems.Thm_Matrix_exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell LanglandsTunnell.CubicInduction

namespace CoeffSmoothAux

noncomputable def archOfRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : NumberField.InfinitePlace ℚ =>
    ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
      (NumberField.IsTotallyReal.isReal v)).symm : ℝ →+* v.Completion)

theorem archRealMat3_eq_mapMatrix (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e =
      AutomorphicForm.archMatrixInclN (Fin 3) ℚ (archOfRealHom.mapMatrix (Matrix.of e)) := by
  unfold WhittakerBlock.archRealMat3
  congr 1

theorem archRealMat3_of_mul (e d : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ) =
      WhittakerBlock.archRealMat3 e * WhittakerBlock.archRealMat3 d := by
  rw [archRealMat3_eq_mapMatrix, archRealMat3_eq_mapMatrix, archRealMat3_eq_mapMatrix,
    ← AutomorphicForm.archMatrixInclN_mul, ← map_mul archOfRealHom.mapMatrix]
  rfl

theorem isUnit_archRealMat3_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  rw [archRealMat3_eq_mapMatrix]
  have h1 : IsUnit (Matrix.of e) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 he)
  exact (h1.map archOfRealHom.mapMatrix).map (AutomorphicForm.archMatrixInclHomN (Fin 3) ℚ)

theorem coe_archRealLift3_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3_of_det_ne_zero he)]
  exact IsUnit.unit_spec _

theorem archRealLift3_of_mul {e d : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0)
    (hd : (Matrix.of d).det ≠ 0) :
    WhittakerBlock.archRealLift3 (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ) =
      WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 d := by
  have hed : (Matrix.of (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
    show (Matrix.of e * Matrix.of d).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero he hd
  apply Units.ext
  rw [Units.val_mul, coe_archRealLift3_of_det_ne_zero he, coe_archRealLift3_of_det_ne_zero hd,
    coe_archRealLift3_of_det_ne_zero hed, archRealMat3_of_mul]

theorem archRealLift3_one_array : WhittakerBlock.archRealLift3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  apply Units.ext
  rw [coe_archRealLift3_of_det_ne_zero (by show (1 : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0; simp),
    archRealMat3_eq_mapMatrix, Units.val_one]
  have h1 : archOfRealHom.mapMatrix (Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1 := by
    rw [show Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ) = (1 : Matrix (Fin 3) (Fin 3) ℝ) from rfl, map_one]
  rw [h1, AutomorphicForm.archMatrixInclN_one]

theorem isOpen_detSet : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have h : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det :=
    (continuous_id (X := Matrix (Fin 3) (Fin 3) ℝ)).matrix_det
  exact isOpen_compl_singleton.preimage h

theorem exists_closedBall_subset_detSet {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall e r ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 isOpen_detSet e he
  exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (half_lt_self hr)).trans hsub⟩

theorem contDiff_det_of : ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  fun_prop

theorem contDiff_adjugate_of (k l : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).adjugate k l := by
  fin_cases k <;> fin_cases l <;>
    simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    fun_prop

theorem contDiffOn_inv_entry (k l : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e)⁻¹ k l)
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have h : ∀ e : Fin 3 → Fin 3 → ℝ, (Matrix.of e)⁻¹ k l = ((Matrix.of e).det)⁻¹ * (Matrix.of e).adjugate k l := by
    intro e
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  simp only [h]
  exact (contDiff_det_of.contDiffOn.inv fun e he => he).mul (contDiff_adjugate_of k l).contDiffOn

theorem continuous_archRealMat3 : Continuous WhittakerBlock.archRealMat3 := by
  refine continuous_matrix fun i j => ?_
  unfold WhittakerBlock.archRealMat3
  simp only [AutomorphicForm.archMatrixInclN, Matrix.of_apply]
  exact (AutomorphicForm.StandardKernel.continuous_ofReal.comp
    ((continuous_apply j).comp (continuous_apply i))).prodMk continuous_const

theorem det_of_inv_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (Matrix.of ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
  show ((Matrix.of e)⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

theorem archRealLift3_inv_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e)⁻¹ =
      WhittakerBlock.archRealLift3 ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h1 : (Matrix.of e * Matrix.of ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    show Matrix.of e * (Matrix.of e)⁻¹ = 1
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 he)
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← archRealLift3_of_mul he (det_of_inv_ne_zero he), h1, archRealLift3_one_array]

theorem continuousOn_archRealLift3_detSet :
    ContinuousOn WhittakerBlock.archRealLift3 {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
        ((WhittakerBlock.archRealLift3 e.1 : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
          WhittakerBlock.archRealMat3 e.1 :=
      fun e => coe_archRealLift3_of_det_ne_zero e.2
    simp only [Set.domRestrict_apply, Function.comp_def, h]
    exact continuous_archRealMat3.comp continuous_subtype_val
  · have h : ∀ e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
        (((WhittakerBlock.archRealLift3 e.1)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
          WhittakerBlock.archRealMat3 ((Matrix.of e.1)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) := by
      intro e
      rw [archRealLift3_inv_of_det_ne_zero e.2]
      exact coe_archRealLift3_of_det_ne_zero (det_of_inv_ne_zero e.2)
    simp only [Set.domRestrict_apply, h]
    refine continuous_archRealMat3.comp ?_
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (contDiffOn_inv_entry k l).continuousOn.comp_continuous continuous_subtype_val fun e => e.2

end CoeffSmoothAux

namespace CoeffSmoothAux

theorem det_ne_zero_of_orth {o : Fin 3 → Fin 3 → ℝ}
    (ho : ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) : (Matrix.of o).det ≠ 0 := by
  have h : (Matrix.of o).transpose * Matrix.of o = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Matrix.transpose_apply, Matrix.of_apply] using ho i j
  intro h0
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem of_arr (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix.of (fun a b => M a b) = M := rfl

theorem contDiffOn_mvPolynomial_eval {s : Set (Fin 3 → Fin 3 → ℝ)} (x : (Fin 3 → Fin 3 → ℝ) → Fin 3 × Fin 3 → ℂ)
    (hx : ∀ ij, ContDiffOn ℝ (⊤ : ℕ∞) (fun e => x e ij) s) (P : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e => MvPolynomial.eval (x e) P) s := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval_C]; exact contDiffOn_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p ij hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (hx ij)

theorem contDiffOn_cpow_of_pos {s : Set (Fin 3 → Fin 3 → ℝ)} (t : (Fin 3 → Fin 3 → ℝ) → ℝ)
    (ht : ContDiffOn ℝ (⊤ : ℕ∞) t s) (hpos : ∀ e ∈ s, 0 < t e) (z : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e => ((t e : ℝ) : ℂ) ^ z) s := by
  have heq : ∀ e ∈ s, Complex.exp (((Real.log (t e) : ℝ) : ℂ) * z) = ((t e : ℝ) : ℂ) ^ z := fun e he => by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (hpos e he).ne'), Complex.ofReal_log (hpos e he).le]
  refine ContDiffOn.congr ?_ (fun e he => (heq e he).symm)
  have hlog : ContDiffOn ℝ (⊤ : ℕ∞) (fun e => Real.log (t e)) s := ht.log fun e he => (hpos e he).ne'
  have hC : ContDiffOn ℝ (⊤ : ℕ∞) (fun e => ((Real.log (t e) : ℝ) : ℂ)) s :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hlog
  exact Complex.contDiff_exp.comp_contDiffOn (hC.mul contDiffOn_const)

theorem main
    (ν : Fin 3 → ℂ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hcont : Continuous F)
    (heq : ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * F g)
    (hfin : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => F (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) :
    WhittakerBlock.IsArchSmooth3 F := by
  classical
  intro g
  obtain ⟨s, hs⟩ := hfin

  set c : Matrix (Fin 3) (Fin 3) ℝ := StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) with hcdef
  have hone : (Matrix.of fun a b : Fin 3 => if a = b then (1 : ℝ) else 0).det ≠ 0 := by
    rw [show (Matrix.of fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) = 1 from by
      ext a b; simp [Matrix.one_apply], Matrix.det_one]
    exact one_ne_zero
  have hc : c.det ≠ 0 := (archRealLift3_mul_eq_mul_archRealLift3_conj g _ hone).1
  have hcunit : IsUnit c.det := isUnit_iff_ne_zero.2 hc
  have hcinv : c⁻¹ * c = 1 := Matrix.nonsing_inv_mul c hcunit
  have hcinv' : c * c⁻¹ = 1 := Matrix.mul_nonsing_inv c hcunit
  have hcinvdet : (c⁻¹).det ≠ 0 := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hc

  have hconj : ∀ m : Matrix (Fin 3) (Fin 3) ℝ, m.det ≠ 0 →
      WhittakerBlock.archRealLift3 (fun a b => m a b) * g =
        g * WhittakerBlock.archRealLift3 (fun a b => (c⁻¹ * m * c) a b) := fun m hm =>
    (archRealLift3_mul_eq_mul_archRealLift3_conj g (fun a b => m a b) hm).2

  let f : (Fin 3 → Fin 3 → ℝ) → ℂ := fun o => F (g * WhittakerBlock.archRealLift3 (fun a b => (c⁻¹ * Matrix.of o) a b))
  have hfcont : ContinuousOn f {o : Fin 3 → Fin 3 → ℝ | ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0} := by
    have hlin : Continuous fun o : Fin 3 → Fin 3 → ℝ => (fun a b => (c⁻¹ * Matrix.of o) a b) :=
      continuous_pi fun a => continuous_pi fun b => by
        simp only [Matrix.mul_apply, Matrix.of_apply]
        exact continuous_finsetSum _ fun k _ => (continuous_const.mul ((continuous_apply b).comp (continuous_apply k)))
    have hmaps : Set.MapsTo (fun o : Fin 3 → Fin 3 → ℝ => (fun a b => (c⁻¹ * Matrix.of o) a b))
        {o : Fin 3 → Fin 3 → ℝ | ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0}
        {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := fun o ho => by
      show (Matrix.of fun a b => (c⁻¹ * Matrix.of o) a b).det ≠ 0
      rw [of_arr, Matrix.det_mul]; exact mul_ne_zero hcinvdet (det_ne_zero_of_orth ho)
    have h1 : ContinuousOn (fun o => WhittakerBlock.archRealLift3 (fun a b => (c⁻¹ * Matrix.of o) a b))
        {o : Fin 3 → Fin 3 → ℝ | ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0} :=
      continuousOn_archRealLift3_detSet.comp hlin.continuousOn hmaps
    exact hcont.comp_continuousOn ((continuousOn_const).mul h1)

  have hffin : ∃ (m : ℕ) (gg : Fin m → (Fin 3 → Fin 3 → ℝ) → ℂ),
      ∀ r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        ∃ a : Fin m → ℂ, ∀ o : Fin 3 → Fin 3 → ℝ,
          (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
          f (fun i j => ∑ k : Fin 3, o i k * r k j) = ∑ l, a l * gg l o := by
    refine ⟨s.card, fun l o => ((s.equivFin.symm l : ↥s) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
      (g * WhittakerBlock.archRealLift3 (fun a b => (c⁻¹ * Matrix.of o) a b)), fun r hr => ?_⟩
    have hrdet : (Matrix.of r).det ≠ 0 := det_ne_zero_of_orth hr
    obtain ⟨hfinite, -, horth⟩ := componentAt3_archRealLift3_eq_one_and_realMat_archComponent3_eq r hrdet
    have hmem := hs (WhittakerBlock.archRealLift3 r) hfinite (horth hr)
    obtain ⟨cf, -, hcf⟩ := Submodule.mem_span_finset.1 hmem
    refine ⟨fun l => cf (s.equivFin.symm l : ↥s), fun o ho => ?_⟩
    have hodet : (Matrix.of fun a b => (c⁻¹ * Matrix.of o) a b).det ≠ 0 := by
      rw [of_arr, Matrix.det_mul]; exact mul_ne_zero hcinvdet (det_ne_zero_of_orth ho)
    have hsplit : WhittakerBlock.archRealLift3 (fun a b => (c⁻¹ * Matrix.of (fun i j => ∑ k : Fin 3, o i k * r k j)) a b) =
        WhittakerBlock.archRealLift3 (fun a b => (c⁻¹ * Matrix.of o) a b) * WhittakerBlock.archRealLift3 r := by
      rw [WhittakerBlock.archRealLift3_mul hodet hrdet]
      congr 1
      funext a b
      simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    show F (g * WhittakerBlock.archRealLift3 (fun a b => (c⁻¹ * Matrix.of (fun i j => ∑ k : Fin 3, o i k * r k j)) a b)) = _
    rw [hsplit, ← mul_assoc]
    have := congrFun hcf (g * WhittakerBlock.archRealLift3 (fun a b => (c⁻¹ * Matrix.of o) a b))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this, ← Finset.sum_coe_sort s, ← Equiv.sum_comp s.equivFin.symm]

  obtain ⟨P, hP⟩ := Matrix.exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates 3 f hfcont hffin
  obtain ⟨bF, oF, hbF, hoF, hIw⟩ := Matrix.exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq 3
  let ce : (Fin 3 → Fin 3 → ℝ) → (Fin 3 → Fin 3 → ℝ) := fun e => fun a b => (c * Matrix.of e) a b
  have hce_det : ∀ e : Fin 3 → Fin 3 → ℝ, (Matrix.of e).det ≠ 0 → (Matrix.of (ce e)).det ≠ 0 := fun e he => by
    show (Matrix.of fun a b => (c * Matrix.of e) a b).det ≠ 0
    rw [of_arr, Matrix.det_mul]; exact mul_ne_zero hc he

  have hformula : ∀ e ∈ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
      (∏ a : Fin 3, ((bF (ce e) a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((oF (ce e) ij.1 ij.2 : ℝ) : ℂ)) P =
        F (g * WhittakerBlock.archRealLift3 e) := by
    intro e he
    obtain ⟨hb_upper, hb_pos, ho_orth, hprod⟩ := hIw (ce e) (hce_det e he)
    have hbdet : (Matrix.of (bF (ce e))).det ≠ 0 := by
      rw [Matrix.det_of_upperTriangular (M := Matrix.of (bF (ce e))) (fun i j hij => hb_upper i j hij)]
      exact Finset.prod_ne_zero_iff.2 fun i _ => (hb_pos i).ne'
    have hodet : (Matrix.of (oF (ce e))).det ≠ 0 := det_ne_zero_of_orth ho_orth
    have hce_eq : c * Matrix.of e = Matrix.of (bF (ce e)) * Matrix.of (oF (ce e)) := by
      ext i j
      have := hprod i j
      simp only [ce, Matrix.mul_apply, Matrix.of_apply] at this ⊢
      exact this
    have h1 : g * WhittakerBlock.archRealLift3 e =
        WhittakerBlock.archRealLift3 (fun a b => (c * Matrix.of e * c⁻¹) a b) * g := by
      rw [hconj (c * Matrix.of e * c⁻¹) (by rw [Matrix.det_mul, Matrix.det_mul]; exact mul_ne_zero (mul_ne_zero hc he) hcinvdet)]
      congr 2
      funext a b
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcinv, Matrix.one_mul, Matrix.mul_assoc, hcinv, Matrix.mul_one,
        Matrix.of_apply]
    have hocdet : (Matrix.of fun a b => (Matrix.of (oF (ce e)) * c⁻¹) a b).det ≠ 0 := by
      rw [of_arr, Matrix.det_mul]; exact mul_ne_zero hodet hcinvdet
    have h2 : WhittakerBlock.archRealLift3 (fun a b => (c * Matrix.of e * c⁻¹) a b) =
        WhittakerBlock.archRealLift3 (bF (ce e)) *
          WhittakerBlock.archRealLift3 (fun a b => (Matrix.of (oF (ce e)) * c⁻¹) a b) := by
      rw [WhittakerBlock.archRealLift3_mul hbdet hocdet]
      congr 1
      funext a b
      show (c * Matrix.of e * c⁻¹) a b = (Matrix.of (bF (ce e)) * Matrix.of (fun a b => (Matrix.of (oF (ce e)) * c⁻¹) a b)) a b
      rw [of_arr (Matrix.of (oF (ce e)) * c⁻¹), ← Matrix.mul_assoc, ← hce_eq]
    have h3 : WhittakerBlock.archRealLift3 (fun a b => (Matrix.of (oF (ce e)) * c⁻¹) a b) * g =
        g * WhittakerBlock.archRealLift3 (fun a b => (c⁻¹ * Matrix.of (oF (ce e))) a b) := by
      rw [hconj (Matrix.of (oF (ce e)) * c⁻¹) (by rw [Matrix.det_mul]; exact mul_ne_zero hodet hcinvdet)]
      congr 2
      funext a b
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hcinv, Matrix.mul_one]
    rw [h1, h2, mul_assoc, heq _ hb_upper hb_pos, h3]
    congr 1
    exact (hP (oF (ce e)) ho_orth).symm

  refine ContDiffOn.congr ?_ (fun e he => (hformula e he).symm)
  have hce_smooth : ContDiff ℝ (⊤ : ℕ∞) ce :=
    contDiff_pi.2 fun a => contDiff_pi.2 fun b => by
      show ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (c * Matrix.of e) a b
      simp only [Matrix.mul_apply, Matrix.of_apply]
      exact ContDiff.sum fun k _ => contDiff_const.mul (contDiff_apply_apply ℝ ℝ k b)
  have hmaps : Set.MapsTo ce {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
    fun e he => hce_det e he
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun e => bF (ce e)) {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
    hbF.comp hce_smooth.contDiffOn hmaps
  have ho : ContDiffOn ℝ (⊤ : ℕ∞) (fun e => oF (ce e)) {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
    hoF.comp hce_smooth.contDiffOn hmaps
  refine ContDiffOn.mul ?_ ?_
  · exact contDiffOn_prod fun a _ => contDiffOn_cpow_of_pos (fun e => bF (ce e) a a)
        ((contDiffOn_pi.1 ((contDiffOn_pi.1 hb) a)) a) (fun e he => (hIw (ce e) (hce_det e he)).2.1 a) _
  · exact contDiffOn_mvPolynomial_eval _ (fun ij => Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_pi.1 ((contDiffOn_pi.1 ho) ij.1)) ij.2)) P

end CoeffSmoothAux

open CoeffSmoothAux in
theorem solution
    (ν : Fin 3 → ℂ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hcont : Continuous F)
    (heq : ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * F g)
    (hfin : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => F (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) :
    WhittakerBlock.IsArchSmooth3 F :=
  CoeffSmoothAux.main ν F hcont heq hfin

end S_LanglandsTunnell_CubicInduction_isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite (solution)
