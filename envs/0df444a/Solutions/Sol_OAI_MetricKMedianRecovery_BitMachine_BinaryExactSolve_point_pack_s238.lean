-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:38:33.782211+00:00
-- url     : https://prove2.me/submissions/74ecb1ae-3bd6-4d88-8fcb-4740e9de23a5

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K021
import Definitions.Def_Q238K022
import Definitions.Def_Q238K024
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryExactSolve_gram_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryExactSolve_rhs_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_RationalMatrix_solveWords_bird_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_finalFace_feasible_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_selectFace_spec_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Freeze
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BirdInteger
open Matrix Function
open scoped BigOperators

section Bridge
variable {R : Type*} [CommRing R] {n : ℕ}
lemma sumFrom_eq_sum_Ico {lo : ℕ} (f : ℕ → R) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih => rw [BirdDet.sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo => rw [BirdDet.sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

lemma sumFrom_fin_tail (i : Fin n) (f : ℕ → R) :
    BirdDet.sumFrom n (i.val + 1) f = ∑ k ∈ Finset.Ioi i, f k.val := calc
  _ = ∑ k ∈ Finset.Ico (i.val + 1) n, f k := by rw [sumFrom_eq_sum_Ico]
  _ = ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by congr; ext; aesop
  _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
  _ = ∑ k : Fin n, if i.val < k.val then f k else 0 := by rw [← Fin.sum_univ_eq_sum_range]
  _ = ∑ k ∈ Finset.Ioi i, f k.val := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

lemma iterate_get_eq_spec (A : Array R) (hA : A.size = n*n) (t : ℕ) (i j : Fin n) :
    ((BirdDet.stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val =
      (BirdDet.Spec.stepEntry (.ofArray A hA))^[t] (.ofArray A hA) i j := by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [BirdDet.get_eq]
  | succ t ih =>
    simp_rw [iterate_succ_apply',BirdDet.stepEntry_eq,BirdDet.Spec.stepEntry_eq,
      sumFrom_fin_tail,ih,Matrix.of_apply,BirdDet.get_eq]

lemma bird_eq_spec (A : Array R) (hA : A.size=n*n) :
    BirdDet.birdDet n A=BirdDet.Spec.birdDet (.ofArray A hA) := by
  cases n with
  | zero => rw [BirdDet.birdDet_zero,BirdDet.Spec.birdDetSpec_zero]
  | succ k => simp [BirdDet.birdDet_succ,BirdDet.Spec.birdDetSpec_succ,←iterate_get_eq_spec A hA k]

lemma spec_eq_det (A : Matrix (Fin n) (Fin n) R) : BirdDet.Spec.birdDet A=A.det := by
  let ar := Array.ofFn (fun k : Fin (n*n) => A k.divNat k.modNat)
  have har : ar.size=n*n := Array.size_ofFn
  have he : Matrix.ofArray ar har=A := Matrix.ofArray_ofFn A
  rw [←he,←bird_eq_spec ar har,←BirdDet.det_eq_birdDet ar har]
end Bridge

lemma iterate_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (t : ℕ) :
    iterate A t=(BirdDet.Spec.stepEntry A)^[t] A := by
  induction t with
  | zero => simp [iterate]
  | succ t ih => simp only [iterate,freeze_eq,ih,iterate_succ_apply']

lemma determinant_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : determinant A=A.det := by
  rw [←spec_eq_det]
  cases n with
  | zero => rfl
  | succ k => simp only [determinant,BirdDet.Spec.birdDetSpec_succ,iterate_eq]

end MetricKMedianRecovery.BirdInteger

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CommonDen
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BirdRational
open Matrix RationalHeight
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma commonDen_pos (q : J → ℚ) : 0 < commonDen q := by
  exact Finset.prod_pos (fun i _ => by exact_mod_cast (q i).den_pos)

lemma scaled_cast (q : J → ℚ) (i : J) :
    (scaled q i:ℚ)=(commonDen q:ℚ)*q i := by
  have hh : commonDen q = (q i).den * ∏ j ∈ Finset.univ.erase i, ((q j).den:ℤ) :=
    (Finset.mul_prod_erase Finset.univ (fun j => ((q j).den:ℤ)) (Finset.mem_univ i)).symm
  have hn : ((q i).den:ℚ)≠0 := by exact_mod_cast (q i).den_nz
  calc
    _ = (commonDen q:ℚ)*((q i).num/(q i).den) := by
      rw [hh]
      unfold scaled
      push_cast
      field_simp
    _ = _ := by rw [Rat.num_div_den]

lemma integerMatrix_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    ((integerMatrix A b).map (Int.cast : ℤ → ℚ))=(commonDen (data A b):ℚ) • A := by
  ext i j
  change ((BirdInteger.freeze (Matrix.of (fun i j => scaled (data A b) (i,some j)))) i j:ℚ) = _
  rw [BirdInteger.freeze_eq]
  exact scaled_cast (data A b) (i,some j)
lemma integerVector_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    (fun i => (integerVector A b i:ℚ))=(commonDen (data A b):ℚ) • b := by
  ext i
  simp [integerVector,scaled_cast,Pi.smul_apply,smul_eq_mul,data]

lemma solve_as_cramer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    solve A b =
      (Matrix.det ((integerMatrix A b).map (Int.cast : ℤ → ℚ)))⁻¹ •
        (Matrix.cramer ((integerMatrix A b).map (Int.cast : ℤ → ℚ)) (fun i => (integerVector A b i:ℚ))) := by
  funext i
  simp [solve,BirdInteger.determinant_eq,Matrix.cramer_apply,Int.cast_det,
    Matrix.map_updateCol,div_eq_mul_inv,mul_comm]
  left
  rfl

theorem solve_correct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (hA : A.det≠0) : A *ᵥ solve A b=b := by
  let D : ℚ := commonDen (data A b)
  have hD : D≠0 := by dsimp [D]; exact_mod_cast (commonDen_pos (data A b)).ne'
  have hZ : Matrix.det ((integerMatrix A b).map (Int.cast : ℤ → ℚ))≠0 := by
    rw [integerMatrix_cast,Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hD) hA
  have he : ((integerMatrix A b).map (Int.cast : ℤ → ℚ)) *ᵥ solve A b =
      (fun i => (integerVector A b i:ℚ)) := by
    rw [solve_as_cramer,Matrix.mulVec_smul,Matrix.mulVec_cramer,smul_smul,inv_mul_cancel₀ hZ,one_smul]
  rw [integerMatrix_cast,integerVector_cast,Matrix.smul_mulVec] at he
  funext i
  exact mul_left_cancel₀ hD (congrFun he i)

end MetricKMedianRecovery.BirdRational

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Region
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
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
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
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
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
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

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Rectangular
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
lemma point_pack_s238_oai {n : ℕ} (rs : List (Row n)) (B : ℕ)
    (hf : ∃ x : Fin n → ℝ, (∀ q∈rs,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    point (pack rs B)=rowEncode (facePoint rs B) := by
  rw [point,gram_pack_s238,rhs_pack_s238,solveWords_bird_s238]
  congr 1
  let C := rowMatrix (finalFace rs B)
  have hC := finalFace_rat_injective rs B hf
  have hG : (C.transpose*C).PosDef := by simpa using PosDef.conjTranspose_mul_self C hC
  have he : BirdRational.solve (C.transpose*C) (C.transpose *ᵥ rowBounds (finalFace rs B))=
      PositiveSolve.solve n (C.transpose*C) (C.transpose *ᵥ rowBounds (finalFace rs B)) := by
    apply mulVec_injective_of_isUnit hG.isUnit
    rw [BirdRational.solve_correct _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit).ne_zero,
      PositiveSolve.solve_correct n _ _ hG]
  simpa only [facePoint,PositiveSolve.freezeMat_eq,PositiveSolve.freezeVec_eq] using he
end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238_oai
