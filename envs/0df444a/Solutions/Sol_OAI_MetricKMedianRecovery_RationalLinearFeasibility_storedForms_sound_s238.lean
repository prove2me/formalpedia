-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:31:17.926397+00:00
-- url     : https://prove2.me/submissions/92b33fa6-b5a1-44b8-994b-54f1e5a131f8

import Mathlib
import Definitions.Def_Q238K022
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_Stored_exactSolve_eq_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_boundedRationalDecide_correct_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_finalFace_feasible_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_selectFace_spec_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Region
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PolytopeCertificate
open Matrix
open scoped Topology BigOperators

variable {R V : Type*} [Fintype R] [Fintype V]

omit [Fintype R] in
lemma row_perturb (A : Matrix R V ℝ) (x u : V → ℝ) (r : R) (t : ℝ) :
    (∑ j, A r j * (x j+t*u j)) = (∑ j, A r j*x j)+t*(∑ j, A r j*u j) := by
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem active_kernel_zero (A : Matrix R V ℝ) (b : R → ℝ) (x : V → ℝ)
    (hx : x ∈ (region A b).extremePoints ℝ) (u : V → ℝ)
    (hu : ∀ r, (∑ j, A r j*x j)=b r → (∑ j, A r j*u j)=0) : u=0 := by
  have hn : ∀ᶠ t : ℝ in 𝓝 0, (fun j => x j+t*u j) ∈ region A b := by
    apply Filter.eventually_all.mpr
    intro r
    by_cases ha : (∑ j, A r j*x j)=b r
    · exact Filter.Eventually.of_forall (fun t => by rw [row_perturb,hu r ha,ha]; simp)
    · have hs : (∑ j, A r j*x j)<b r := lt_of_le_of_ne (hx.1 r) ha
      have hc : Continuous (fun t : ℝ => ∑ j, A r j*(x j+t*u j)) := by fun_prop
      have hh : ∀ᶠ t : ℝ in 𝓝 0, (∑ j, A r j*(x j+t*u j))<b r :=
        hc.continuousAt.eventually_lt_const (by simpa using hs)
      exact hh.mono (fun _ h => h.le)
  obtain ⟨e,he,hs⟩ := Metric.eventually_nhds_iff.mp hn
  have hp : (fun j => x j+(e/2)*u j) ∈ region A b := hs (by simpa [abs_of_pos he] using (show e/2<e by linarith))
  have hm : (fun j => x j+(-e/2)*u j) ∈ region A b := hs (by simpa [abs_of_pos he] using (show e/2<e by linarith))
  have hmid : midpoint ℝ (fun j => x j+(e/2)*u j) (fun j => x j+(-e/2)*u j) = x := by
    rw [midpoint_eq_smul_add]
    ext j
    simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul,invOf_eq_inv]
    ring
  have hseg := midpoint_mem_openSegment (𝕜 := ℝ) (fun j => x j+(e/2)*u j) (fun j => x j+(-e/2)*u j)
  rw [hmid] at hseg
  have heq := hx.2 hp hm hseg
  ext j
  have hh := congrFun heq j
  change u j=0
  have hmul : (e/2)*u j=0 := by linarith
  exact (mul_eq_zero.mp hmul).resolve_left (by positivity)

omit [Fintype R] in
lemma region_closed (A : Matrix R V ℝ) (b : R → ℝ) : IsClosed (region A b) := by
  have h : region A b = ⋂ r, {x : V → ℝ | (∑ j, A r j*x j) ≤ b r} := by
    ext x
    simp only [region,Set.mem_ofPred_eq,Set.mem_iInter]
  rw [h]
  apply isClosed_iInter
  intro r
  exact isClosed_le (by fun_prop) continuous_const

theorem bounded_extreme (A : Matrix R V ℝ) (b : R → ℝ) (B : ℝ)
    (hn : (region A b).Nonempty)
    (hbound : ∀ x ∈ region A b, ∀ j, -B ≤ x j ∧ x j ≤ B) :
    ∃ x ∈ region A b, ∀ u : V → ℝ,
      (∀ r, (∑ j, A r j*x j)=b r → (∑ j, A r j*u j)=0) → u=0 := by
  have hc : IsCompact (region A b) :=
    isCompact_Icc.of_isClosed_subset (region_closed A b) (by
      intro x hx
      exact ⟨fun j => (hbound x hx j).1,fun j => (hbound x hx j).2⟩)
  obtain ⟨x,hx⟩ := hc.extremePoints_nonempty hn
  exact ⟨x,hx.1,fun u hu => active_kernel_zero A b x hx u hu⟩

end MetricKMedianRecovery.PolytopeCertificate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility

lemma Row.realHolds_cast {n : ℕ} (r : Row n) (x : Fin n → ℚ) :
    r.RealHolds (fun i => (x i : ℝ)) ↔ r.Holds x := by
  unfold Row.RealHolds Row.realValue Row.Holds Row.value
  dsimp only
  norm_cast

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EnumeratedRow
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility
variable {V R : Type*} [Fintype V] {n : ℕ}

lemma Form.enumeratedRow_holds (e : Fin n ≃ V) (f : Form V) (x : Fin n → ℚ) :
    (f.enumeratedRow e).Holds x ↔ f.eval (fun v => x (e.symm v)) ≤ 0 := by
  unfold Row.Holds Row.value Form.enumeratedRow Form.eval
  have he := e.sum_comp (fun v => f.coeff v * x (e.symm v))
  simp only [Equiv.symm_apply_apply] at he
  rw [he]
  constructor <;> intro h <;> linarith

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ReverseRow
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

lemma reverseRow_holds {n : ℕ} (q : Row n) (x : Fin n → ℝ) :
    (reverseRow q).RealHolds x ↔ (q.bound:ℝ)≤q.realValue x := by
  simp [reverseRow,Row.RealHolds,Row.realValue,Finset.sum_neg_distrib]

lemma faceRows_holds {n : ℕ} (rows picked : List (Row n)) (x : Fin n → ℝ) :
    (∀ q∈faceRows rows picked, q.RealHolds x) ↔
      (∀ q∈rows, q.RealHolds x) ∧ (∀ q∈picked, q.realValue x=(q.bound:ℝ)) := by
  constructor
  · intro h
    refine ⟨fun q hq => h q (List.mem_append_left _ (List.mem_append_left _ hq)),?_⟩
    intro q hq
    have hp := h q (List.mem_append_left _ (List.mem_append_right _ hq))
    have hm := h (reverseRow q) (List.mem_append_right _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    exact le_antisymm hp ((reverseRow_holds _ _).mp hm)
  · rintro ⟨ha,hp⟩ q hq
    rcases List.mem_append.mp hq with hq|hq
    · rcases List.mem_append.mp hq with hq|hq
      · exact ha q hq
      · exact (hp q hq).le
    · obtain ⟨p,hp0,he⟩ := List.mem_map.mp hq
      subst q
      exact (reverseRow_holds _ _).mpr (hp p hp0).ge

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoordinateRow
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

lemma coordinateRow_value {n : ℕ} (i : Fin n) (c b : ℚ) (x : Fin n → ℝ) :
    (coordinateRow i c b).realValue x=(c:ℝ)*x i := by
  simp [coordinateRow,Row.realValue,apply_ite]

lemma boxRows_holds {n B : ℕ} (x : Fin n → ℝ) :
    (∀ q∈boxRows n B, q.RealHolds x) ↔ ∀ j, |x j|≤(B:ℝ) := by
  have he (i : Fin n) (c : ℚ) : (coordinateRow i c B).RealHolds x ↔ (c:ℝ)*x i≤(B:ℝ) := by
    change (coordinateRow i c B).realValue x≤((B:ℚ):ℝ) ↔ _
    rw [coordinateRow_value,Rat.cast_natCast]
  simp only [boxRows,List.forall_mem_append,List.forall_mem_ofFn_iff,he]
  constructor
  · rintro ⟨hp,hm⟩ j
    have hpj : x j≤(B:ℝ) := by simpa using hp j
    have hmj : -x j≤(B:ℝ) := by simpa using hm j
    exact abs_le.mpr ⟨by linarith,hpj⟩
  · intro h
    constructor
    · intro j
      simpa using (abs_le.mp (h j)).2
    · intro j
      have hh := (abs_le.mp (h j)).1
      simpa using (show -x j≤(B:ℝ) by linarith)

lemma rowMatrix_region {n : ℕ} (rows : List (Row n)) (x : Fin n → ℝ) :
    x∈region (fun i j => (rowMatrix rows i j:ℝ)) (fun i => (rowBounds rows i:ℝ)) ↔
      ∀ q∈rows, q.RealHolds x := by
  constructor
  · intro h q hq
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hq
    have hh : rows[i].RealHolds x := h ⟨i,hi⟩
    rwa [he] at hh
  · intro h i
    exact h _ (List.getElem_mem _)

theorem finalFace_kernel {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ)))
    (u : Fin n → ℝ) (hu : ∀ q∈finalFace rows B, ∑ j, (q.coeff j:ℝ)*u j=0) : u=0 := by
  let base := withBox rows B
  let picked := finalFace rows B
  let all := faceRows base picked
  obtain ⟨x0,hx0⟩ := finalFace_feasible_s238 rows B hfeas
  have hbox (x : Fin n → ℝ) (hx : ∀ q∈all, q.RealHolds x) : ∀ j, |x j|≤(B:ℝ) := by
    have hh := (faceRows_holds base picked x).mp hx
    exact (boxRows_holds x).mp (fun q hq => hh.1 q (List.mem_append_right _ hq))
  obtain ⟨x,hx,hker⟩ := bounded_extreme (fun i j => (rowMatrix all i j:ℝ))
    (fun i => (rowBounds all i:ℝ)) B
    ⟨x0,(rowMatrix_region all x0).mpr ((faceRows_holds base picked x0).mpr ⟨hx0.1,hx0.2.1⟩)⟩
    (fun x hx j => abs_le.mp (hbox x ((rowMatrix_region all x).mp hx) j))
  have hxp : Face base picked B x := by
    have hh := (rowMatrix_region all x).mp hx
    have hf := (faceRows_holds base picked x).mp hh
    exact ⟨hf.1,hf.2,hbox x hh⟩
  have hf0 : ∃ y, Face base [] B y := ⟨x0,⟨hx0.1,by simp,hx0.2.2⟩⟩
  have hactive := (selectFace_spec_s238 base B base [] hf0).2.2 x hxp
  apply hker u
  intro i hi
  have hm : all[i]∈all := List.getElem_mem _
  change all[i].realValue x=(all[i].bound:ℝ) at hi
  change (∑ j, (all[i].coeff j:ℝ)*u j)=0
  rcases List.mem_append.mp hm with hm|hm
  · rcases List.mem_append.mp hm with hm|hm
    · exact hu _ (hactive _ hm hi)
    · exact hu _ hm
  · obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
    rw [←he]
    simp only [reverseRow,Rat.cast_neg,neg_mul,Finset.sum_neg_distrib,hu q hq,neg_zero]

end MetricKMedianRecovery.Ellipsoid

namespace MetricKMedianRecovery.PositiveSolve
open Matrix
open scoped BigOperators

lemma schur_mulVec {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (x : Fin n → ℚ) (i : Fin n) :
    (schur M *ᵥ x) i = (∑ j, M i.succ j.succ*x j)-
      M i.succ 0*(∑ j, M 0 j.succ*x j)/M 0 0 := by
  simp only [mulVec,dotProduct,schur,sub_mul,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma schur_isHermitian {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hM : M.IsHermitian) : (schur M).IsHermitian := by
  have he (i j : Fin (n+1)) : M j i=M i j := by simpa using congrFun (congrFun hM i) j
  ext i j
  simp only [conjTranspose_apply,star_trivial,schur]
  rw [he j.succ i.succ,he 0 i.succ,he j.succ 0]
  ring

lemma schur_posDef {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hM : M.PosDef) : (schur M).PosDef := by
  apply posDef_iff_dotProduct_mulVec.mpr
  refine ⟨schur_isHermitian M hM.1,?_⟩
  intro x hx
  let z : Fin (n+1) → ℚ := Fin.cons (-(∑ j, M 0 j.succ*x j)/M 0 0) x
  have hz : z≠0 := by
    intro he
    apply hx
    funext j
    exact congrFun he j.succ
  have hd : M 0 0≠0 := hM.diag_pos.ne'
  have hh : (M *ᵥ z) 0=0 := by
    simp only [mulVec,dotProduct,Fin.sum_univ_succ,z,Fin.cons_zero,Fin.cons_succ]
    field_simp
    ring
  have ht (i : Fin n) : (M *ᵥ z) i.succ=(schur M *ᵥ x) i := by
    rw [schur_mulVec]
    simp only [mulVec,dotProduct,Fin.sum_univ_succ,z,Fin.cons_zero,Fin.cons_succ]
    ring
  have hp := hM.dotProduct_mulVec_pos hz
  simpa only [star_trivial,dotProduct,Fin.sum_univ_succ,hh,mul_zero,zero_add,z,Fin.cons_succ,ht] using hp

theorem solve_correct (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (hM : M.PosDef) : M *ᵥ solve n M b=b := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have hd : M 0 0≠0 := hM.diag_pos.ne'
    have hx := ih (schur M) (rhs M b) (schur_posDef M hM)
    simp only [solve,freezeVec_eq,freezeMat_eq]
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [mulVec,dotProduct,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
      field_simp
      ring
    · have hi := congrFun hx i
      rw [schur_mulVec] at hi
      simp only [mulVec,dotProduct,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
      dsimp [rhs] at hi
      linear_combination hi

end MetricKMedianRecovery.PositiveSolve

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FacePoint
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

lemma finalFace_injective {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    Function.Injective (fun u : Fin n → ℝ =>
      (fun i j => (rowMatrix (finalFace rows B) i j:ℝ)) *ᵥ u) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply finalFace_kernel rows B hfeas
  intro q hq
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hq
  have hh := congrFun huv ⟨i,hi⟩
  change (∑ j, ((finalFace rows B)[i].coeff j:ℝ)*u j)=
    (∑ j, ((finalFace rows B)[i].coeff j:ℝ)*v j) at hh
  rw [he] at hh
  simpa only [Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,sub_eq_zero] using hh

lemma finalFace_rat_injective {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    Function.Injective (rowMatrix (finalFace rows B)).mulVec := by
  intro u v huv
  have he := finalFace_injective rows B hfeas (a₁:=fun j => (u j:ℝ)) (a₂:=fun j => (v j:ℝ)) ?_
  · funext j
    exact_mod_cast congrFun he j
  · ext i
    have hh := congrFun huv i
    change (∑ j, (rowMatrix (finalFace rows B) i j:ℝ)*(u j:ℝ))=
      (∑ j, (rowMatrix (finalFace rows B) i j:ℝ)*(v j:ℝ))
    exact_mod_cast hh

theorem facePoint_correct {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    Face (withBox rows B) (finalFace rows B) B (fun j => (facePoint rows B j:ℝ)) := by
  let picked := finalFace rows B
  let C := rowMatrix picked
  let Cr : Matrix (Fin picked.length) (Fin n) ℝ := fun i j => (C i j:ℝ)
  have hC : Function.Injective C.mulVec := finalFace_rat_injective rows B hfeas
  have hCr : Function.Injective Cr.mulVec := finalFace_injective rows B hfeas
  have hG : (Cᵀ*C).PosDef := by simpa using PosDef.conjTranspose_mul_self C hC
  have hGr : (Crᵀ*Cr).PosDef := by simpa using PosDef.conjTranspose_mul_self Cr hCr
  obtain ⟨x,hx⟩ := finalFace_feasible_s238 rows B hfeas
  have hxe : Cr *ᵥ x=fun i => (rowBounds picked i:ℝ) := by
    ext i
    exact hx.2.1 _ (List.getElem_mem _)
  have hy : (Cᵀ*C) *ᵥ facePoint rows B=Cᵀ *ᵥ rowBounds picked := by
    simpa only [facePoint,PositiveSolve.freezeMat_eq,PositiveSolve.freezeVec_eq] using
      PositiveSolve.solve_correct n (Cᵀ*C) (Cᵀ *ᵥ rowBounds picked) hG
  have hye : (Crᵀ*Cr) *ᵥ (fun j => (facePoint rows B j:ℝ))=
      Crᵀ *ᵥ (fun i => (rowBounds picked i:ℝ)) := by
    ext i
    have hh := congrFun hy i
    change (∑ j, (∑ k, (C k i:ℝ)*(C k j:ℝ))*(facePoint rows B j:ℝ))=
      (∑ k, (C k i:ℝ)*(rowBounds picked k:ℝ))
    exact_mod_cast hh
  have he : (fun j => (facePoint rows B j:ℝ))=x := by
    apply mulVec_injective_of_isUnit hGr.isUnit
    rw [hye,←mulVec_mulVec,hxe]
  rwa [he]

theorem exactSolve_some {n : ℕ} (rows : List (Row n)) (B : ℕ) (x : Fin n → ℚ)
    (hx : exactSolve rows B=some x) :
    (∀ q∈rows,q.Holds x) ∧ (∀ j,|x j|≤(B:ℚ)) := by
  unfold exactSolve at hx
  split at hx
  next hd =>
    have he := Option.some.inj hx
    subst x
    have hh := facePoint_correct rows B ((boundedRationalDecide_correct_s238 rows B).mp hd)
    refine ⟨?_,?_⟩
    · intro q hq
      exact (Row.realHolds_cast _ _).mp (hh.1 q (List.mem_append_left _ hq))
    · intro j
      have hj : |(facePoint rows B j:ℝ)|≤(B:ℝ) := hh.2.2 j
      exact_mod_cast hj
  next => contradiction

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid.Stored
open Matrix RationalLinearFeasibility
open scoped BigOperators

theorem exactSolve_some {n : ℕ} (rows : List (Row n)) (B : ℕ) (x : Fin n → ℚ)
    (hx : exactSolve rows B=some x) :
    (∀ q∈rows,q.Holds x) ∧ (∀ j,|x j|≤(B:ℚ)) :=
  Ellipsoid.exactSolve_some rows B x (by simpa only [exactSolve_eq_s238] using hx)

end MetricKMedianRecovery.Ellipsoid.Stored

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StoredForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility
open scoped BigOperators
variable {V R : Type*} [Fintype V] {n : ℕ}

lemma storedForms_sound_s238_oai (e : Fin n ≃ V) (rows : List R) (f : R → Form V) (B : ℕ)
    (x : V → ℚ) (hx : storedForms e rows f B=some x) :
    (∀ r∈rows,(f r).eval x≤0) ∧ (∀ j,|x j|≤(B:ℚ)) := by
  obtain ⟨y,hy,rfl⟩ := Option.map_eq_some_iff.mp hx
  have hs := Ellipsoid.Stored.exactSolve_some _ B y hy
  exact ⟨fun r hr => ((f r).enumeratedRow_holds e y).mp
    (hs.1 _ (List.mem_map.mpr ⟨r,hr,rfl⟩)),fun j => hs.2 (e.symm j)⟩

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238_oai.{u_1, u_2} := @OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238_oai.{u_1, u_2}
