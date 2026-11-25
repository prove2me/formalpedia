-- Prove2me | solution 1 for IntConeFPT.short_recession_step
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T09:28:30.329329+00:00
-- url     : https://prove2.me/submissions/b3aaf45e-88e2-42ca-b1db-5f96d36fce42

import Mathlib

open Matrix
namespace IntConeFPT.Recession
open scoped Classical
lemma abs_det_le_fact_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hB : ∀ i j, |A i j| ≤ (B : ℤ)) :
    |A.det| ≤ (n.factorial * B ^ n : ℕ) := by
  rw [Matrix.det_apply']
  calc |∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i)|
    _ ≤ ∑ σ : Equiv.Perm (Fin n), |(Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin n), |∏ i, A (σ i) i| := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [abs_mul]
        have hs : |(Equiv.Perm.sign σ : ℤ)| = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [hs, one_mul]
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), (B : ℤ) ^ n := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [Finset.abs_prod]
        calc ∏ i : Fin n, |A (σ i) i|
          _ ≤ ∏ _i : Fin n, (B : ℤ) :=
              Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hB (σ i) i)
          _ = (B : ℤ) ^ n := by simp
    _ = (n.factorial * B ^ n : ℕ) := by
        simp [Fintype.card_perm, Fintype.card_fin]

def cofactorVec {q : ℕ} (F : Matrix (Fin (q + 1)) (Fin q) ℤ) : Fin (q + 1) → ℤ :=
  fun a => (-1 : ℤ) ^ (a : ℕ) * (F.submatrix a.succAbove id).det

lemma cofactorVec_bound {q : ℕ} (F : Matrix (Fin (q + 1)) (Fin q) ℤ) (B : ℕ)
    (hB : ∀ a j, |F a j| ≤ (B : ℤ)) (a : Fin (q + 1)) :
    |cofactorVec F a| ≤ (q.factorial * B ^ q : ℕ) := by
  unfold cofactorVec
  rw [abs_mul]
  have hsign : |(-1 : ℤ) ^ (a : ℕ)| = 1 := by simp [abs_pow]
  rw [hsign, one_mul]
  exact abs_det_le_fact_pow (F.submatrix a.succAbove id) B fun i j => hB _ _

lemma cofactorVec_orth {q : ℕ} (F : Matrix (Fin (q + 1)) (Fin q) ℤ) (j : Fin q) :
    ∑ a : Fin (q + 1), cofactorVec F a * F a j = 0 := by
  let G : Matrix (Fin (q + 1)) (Fin (q + 1)) ℤ :=
    Matrix.of fun a l => Fin.cases (F a j) (fun j' => F a j') l
  have hzero : G.det = 0 := by
    refine Matrix.det_zero_of_column_eq (Fin.succ_ne_zero j).symm fun k => ?_
    simp [G]
  rw [Matrix.det_succ_column_zero] at hzero
  have hid : ∑ a : Fin (q + 1), (-1 : ℤ) ^ (a : ℕ) * G a 0 * (G.submatrix a.succAbove Fin.succ).det =
      ∑ a : Fin (q + 1), cofactorVec F a * F a j := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have hsub : G.submatrix a.succAbove Fin.succ = F.submatrix a.succAbove id := by
      ext i l
      simp [G]
    rw [hsub]
    simp only [G, Matrix.of_apply, Fin.cases_zero, cofactorVec]
    ring
  rw [← hid]
  exact hzero

private lemma det_ne_zero_of_cols_indep {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : LinearIndependent ℝ (fun l : Fin n => fun a : Fin n => H a l)) :
    H.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hHv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := H)).mpr hdet
  apply hv0
  have hlin : ∑ l : Fin n, v l • (fun a : Fin n => H a l) = 0 := by
    ext a
    have ha := congrFun hHv a
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using ha
  exact funext ((Fintype.linearIndependent_iff.mp hH) v hlin)

private lemma det_col0_update_cols_indep {q : ℕ} (F : Matrix (Fin (q + 1)) (Fin q) ℤ)
    (hF : LinearIndependent ℝ (fun j : Fin q => fun a : Fin (q + 1) => (F a j : ℝ)))
    (w : Fin (q + 1) → ℝ) (hw0 : w ≠ 0)
    (hwF : ∀ j : Fin q, ∑ a : Fin (q + 1), w a * (F a j : ℝ) = 0) :
    (Matrix.of (fun a l => Fin.cases (motive := fun _ => ℝ) (w a) (fun j => (F a j : ℝ)) l)).det ≠ 0 := by
  let H : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
    Matrix.of fun a l => Fin.cases (motive := fun _ => ℝ) (w a) (fun j => (F a j : ℝ)) l
  change H.det ≠ 0
  refine det_ne_zero_of_cols_indep H ?_
  rw [Fintype.linearIndependent_iff]
  intro α hα
  have hdot : ∑ a : Fin (q + 1), w a * (∑ l : Fin (q + 1), α l * H a l) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    have ha := congrFun hα a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ha
    rw [show ∑ l, α l * H a l = ∑ l, H a l * α l from Finset.sum_congr rfl fun _ _ => mul_comm _ _]
    have ha' : ∑ l, H a l * α l = 0 := by
      simpa [mul_comm] using ha
    rw [ha', mul_zero]
  simp_rw [Finset.mul_sum] at hdot
  rw [Finset.sum_comm] at hdot
  have hdot2 : ∑ l : Fin (q + 1), α l * (∑ a : Fin (q + 1), w a * H a l) = 0 := by
    rw [← hdot]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [Fin.sum_univ_succ] at hdot2
  have hrest0 : ∑ j : Fin q, α j.succ * (∑ a, w a * H a j.succ) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj := hwF j
    simp only [H, Matrix.of_apply, Fin.cases_succ]
    rw [hj, mul_zero]
  rw [hrest0, add_zero] at hdot2
  have hw_sq_pos : 0 < ∑ a : Fin (q + 1), w a * H a 0 := by
    simp only [H, Matrix.of_apply, Fin.cases_zero]
    have hex : ∃ a₀ : Fin (q + 1), w a₀ ≠ 0 := by
      by_contra hnone
      push Not at hnone
      exact hw0 (funext hnone)
    obtain ⟨a₀, ha₀⟩ := hex
    exact Finset.sum_pos' (fun a _ => mul_self_nonneg (w a))
      ⟨a₀, Finset.mem_univ a₀, mul_self_pos.mpr ha₀⟩
  have hα0 : α 0 = 0 := (mul_eq_zero.mp hdot2).resolve_right hw_sq_pos.ne'
  have htail : ∑ j : Fin q, α j.succ • (fun a : Fin (q + 1) => (F a j : ℝ)) = 0 := by
    ext a
    have ha := congrFun hα a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ha ⊢
    rw [Fin.sum_univ_succ, hα0, zero_mul, zero_add] at ha
    simpa [H] using ha
  have hα_succ : ∀ j : Fin q, α j.succ = 0 := (Fintype.linearIndependent_iff.mp hF) _ htail
  intro l
  refine Fin.cases hα0 hα_succ l

private lemma cofactorVec_dot_eq_det {q : ℕ} (F : Matrix (Fin (q + 1)) (Fin q) ℤ)
    (w : Fin (q + 1) → ℝ) :
    (Matrix.of (fun a l => Fin.cases (motive := fun _ => ℝ) (w a) (fun j => (F a j : ℝ)) l)).det =
      ∑ a : Fin (q + 1), w a * (cofactorVec F a : ℝ) := by
  let H : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
    Matrix.of fun a l => Fin.cases (motive := fun _ => ℝ) (w a) (fun j => (F a j : ℝ)) l
  change H.det = _
  rw [Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsub : H.submatrix a.succAbove Fin.succ =
      (Int.castRingHom ℝ).mapMatrix (F.submatrix a.succAbove id) := by
    ext i j
    simp [H]
  rw [hsub, ← RingHom.map_det]
  simp only [H, Matrix.of_apply, Fin.cases_zero, cofactorVec, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.coe_castRingHom]
  ring

lemma cofactorVec_proportional_of_orth {q : ℕ} (F : Matrix (Fin (q + 1)) (Fin q) ℤ)
    (hF : LinearIndependent ℝ (fun j : Fin q => fun a : Fin (q + 1) => (F a j : ℝ)))
    (y : Fin (q + 1) → ℝ) (hy0 : y ≠ 0)
    (hyF : ∀ j : Fin q, ∑ a : Fin (q + 1), y a * (F a j : ℝ) = 0) :
    (cofactorVec F ≠ 0) ∧
    (∀ v : Fin (q + 1) → ℝ, (∀ j : Fin q, ∑ a : Fin (q + 1), v a * (F a j : ℝ) = 0) →
      ∃ c : ℝ, v = c • y) ∧
    ∃ α : ℝ, α ≠ 0 ∧ (fun a => (cofactorVec F a : ℝ)) = α • y := by
  let uR : Fin (q + 1) → ℝ := fun a => (cofactorVec F a : ℝ)
  have hdet_ne : ∑ a : Fin (q + 1), y a * uR a ≠ 0 := by
    rw [← cofactorVec_dot_eq_det F y]
    exact det_col0_update_cols_indep F hF y hy0 hyF
  have hcf0 : cofactorVec F ≠ 0 := by
    intro hz
    apply hdet_ne
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [uR, hz]
  have hunique : ∀ v : Fin (q + 1) → ℝ,
      (∀ j : Fin q, ∑ a : Fin (q + 1), v a * (F a j : ℝ) = 0) →
      ∃ c : ℝ, v = c • y := by
    intro v hvF
    let D := ∑ a : Fin (q + 1), y a * uR a
    let c := (∑ a : Fin (q + 1), v a * uR a) / D
    refine ⟨c, ?_⟩
    let w := v - c • y
    have hwF : ∀ j : Fin q, ∑ a : Fin (q + 1), w a * (F a j : ℝ) = 0 := by
      intro j
      calc ∑ a, w a * (F a j : ℝ)
        _ = (∑ a, v a * (F a j : ℝ)) - c * (∑ a, y a * (F a j : ℝ)) := by
            simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
              Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
        _ = 0 := by rw [hvF j, hyF j, mul_zero, sub_zero]
    have hwu : ∑ a : Fin (q + 1), w a * uR a = 0 := by
      calc ∑ a, w a * uR a
        _ = (∑ a, v a * uR a) - c * D := by
            simp only [w, D, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
              Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
        _ = 0 := by rw [div_mul_cancel₀ _ hdet_ne, sub_self]
    have hw0 : w = 0 := by
      by_contra hwnz
      have hdet0 := det_col0_update_cols_indep F hF w hwnz hwF
      rw [cofactorVec_dot_eq_det F w] at hdet0
      exact hdet0 hwu
    exact sub_eq_zero.mp hw0
  have huR_orth : ∀ j : Fin q, ∑ a : Fin (q + 1), uR a * (F a j : ℝ) = 0 := by
    intro j
    have hz : ((∑ a : Fin (q + 1), cofactorVec F a * F a j : ℤ) : ℝ) = 0 := by
      rw [cofactorVec_orth F j]; simp
    simpa [uR, Int.cast_sum, Int.cast_mul] using hz
  obtain ⟨α, hα⟩ := hunique uR huR_orth
  have hα0 : α ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hα
    exact hcf0 (funext fun a => by
      have ha : (cofactorVec F a : ℝ) = (0 : ℝ) := congrFun hα a
      exact_mod_cast ha)
  exact ⟨hcf0, hunique, α, hα0, hα⟩

/-! ## 3. Bounded Integral Farkas Projection -/

noncomputable def tightRows {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
    (lam : Fin p → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => ((A.map (Int.cast : ℤ → ℝ)) *ᵥ lam) i = (b i : ℝ)

noncomputable def tightSpan {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
    (lam : Fin p → ℝ) : Submodule ℝ (Fin p → ℝ) :=
  Submodule.span ℝ ((fun i : Fin m => fun j : Fin p => (A i j : ℝ)) '' (tightRows A b lam : Set (Fin m)))

noncomputable def tightRank {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
    (lam : Fin p → ℝ) : ℕ :=
  Module.finrank ℝ (tightSpan A b lam)

private lemma tightRank_le {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
    (lam : Fin p → ℝ) : tightRank A b lam ≤ p := by
  simpa [tightRank, Module.finrank_fin_fun] using Submodule.finrank_le (tightSpan A b lam)

private lemma row_basis_of_finset {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (T : Finset (Fin m)) :
    let rowR : Fin m → (Fin p → ℝ) := fun i j => (A i j : ℝ)
    let S := Submodule.span ℝ (rowR '' (T : Set (Fin m)))
    let q := Module.finrank ℝ S
    ∃ B : Fin q → Fin m,
      (∀ l, B l ∈ T) ∧
      LinearIndependent ℝ (fun l : Fin q => rowR (B l)) ∧
      Submodule.span ℝ (Set.range (fun l : Fin q => rowR (B l))) = S ∧
      (∀ u : Fin p → ℝ, (∀ l : Fin q, ((A.map (Int.cast : ℤ → ℝ)) *ᵥ u) (B l) = 0) ↔
        ∀ i ∈ T, ((A.map (Int.cast : ℤ → ℝ)) *ᵥ u) i = 0) := by
  intro rowR S q
  obtain ⟨b_set, hb_sub, hb_span, hb_indep⟩ :=
    exists_linearIndependent ℝ (rowR '' (T : Set (Fin m)))
  have hb_fin : b_set.Finite := Set.Finite.subset (T.finite_toSet.image rowR) hb_sub
  let J := hb_fin.toFinset
  have hJ_coe : (J : Set (Fin p → ℝ)) = b_set := hb_fin.coe_toFinset
  let r := J.card
  let eJ : Fin r ≃ J := (Fintype.equivFinOfCardEq (Fintype.card_coe J)).symm
  have hpick : ∀ v : J, ∃ i ∈ T, rowR i = v.1 := fun v => by
    have hv : v.1 ∈ b_set := by rw [← hJ_coe]; exact Finset.mem_coe.mpr v.2
    exact hb_sub hv
  choose B_raw hB_T hB_eq using fun l : Fin r => hpick (eJ l)
  have hB_indep : LinearIndependent ℝ (fun l : Fin r => rowR (B_raw l)) := by
    have heq : (fun l : Fin r => rowR (B_raw l)) = Subtype.val ∘ eJ := by
      ext l j; exact congrFun (hB_eq l) j
    rw [heq]
    have hJ_indep : LinearIndependent ℝ (Subtype.val : J → (Fin p → ℝ)) :=
      hb_indep.comp (fun x : J => ⟨x.1, by rw [← hJ_coe]; exact x.2⟩)
        fun _ _ h => Subtype.ext (congrArg (Subtype.val : b_set → Fin p → ℝ) h)
    exact hJ_indep.comp eJ eJ.injective
  have hB_span : Submodule.span ℝ (Set.range (fun l : Fin r => rowR (B_raw l))) = S := by
    have hrange : Set.range (fun l : Fin r => rowR (B_raw l)) = b_set := by
      ext v
      constructor
      · rintro ⟨l, rfl⟩
        dsimp only
        rw [hB_eq l, ← hJ_coe]
        exact Finset.mem_coe.mpr (eJ l).2
      · intro hv
        have hvJ : v ∈ J := by rw [← Finset.mem_coe, hJ_coe]; exact hv
        obtain ⟨l, hl⟩ := eJ.surjective ⟨v, hvJ⟩
        exact ⟨l, by dsimp only; rw [hB_eq l, hl]⟩
    rw [hrange, hb_span]
  have hq_eq : r = q := by
    change r = Module.finrank ℝ S
    rw [← hB_span, finrank_span_eq_card hB_indep, Fintype.card_fin]
  let e_rq : Fin q ≃ Fin r := finCongr hq_eq.symm
  have hrange_rq : Set.range (fun l : Fin q => rowR ((B_raw ∘ e_rq) l)) =
      Set.range (fun l : Fin r => rowR (B_raw l)) := by
    ext v
    constructor
    · rintro ⟨l, rfl⟩; exact ⟨e_rq l, rfl⟩
    · rintro ⟨l, rfl⟩; exact ⟨e_rq.symm l, by simp⟩
  refine ⟨B_raw ∘ e_rq, fun l => hB_T (e_rq l), ?_, ?_, ?_⟩
  · exact hB_indep.comp e_rq e_rq.injective
  · rw [hrange_rq, hB_span]
  · intro u
    constructor
    · intro hu i hi
      have hiS : rowR i ∈ Submodule.span ℝ (Set.range (fun l : Fin q => rowR ((B_raw ∘ e_rq) l))) := by
        rw [hrange_rq, hB_span]
        exact Submodule.subset_span ⟨i, hi, rfl⟩
      rw [Finsupp.mem_span_range_iff_exists_finsupp] at hiS
      obtain ⟨c, hc⟩ := hiS
      have hdot : ((A.map (Int.cast : ℤ → ℝ)) *ᵥ u) i = ∑ j : Fin p, rowR i j * u j := by
        simp [Matrix.mulVec, dotProduct, rowR]
      rw [hdot, ← hc]
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l _ => ?_
      have hl := hu l
      have hl' : ∑ j : Fin p, rowR (B_raw (e_rq l)) j * u j = 0 := by
        simpa [Matrix.mulVec, dotProduct, rowR] using hl
      calc ∑ j : Fin p, c l * rowR (B_raw (e_rq l)) j * u j
        _ = c l * ∑ j : Fin p, rowR (B_raw (e_rq l)) j * u j := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by rw [hl', mul_zero]
    · intro hu l
      exact hu _ (hB_T (e_rq l))

private lemma tightRank_lt_insert {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (T : Finset (Fin m))
    (i₀ : Fin m) (u : Fin p → ℝ)
    (huT : ∀ i ∈ T, ((A.map (Int.cast : ℤ → ℝ)) *ᵥ u) i = 0)
    (hu0 : ((A.map (Int.cast : ℤ → ℝ)) *ᵥ u) i₀ ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ ((fun i j => (A i j : ℝ)) '' (T : Set (Fin m)))) <
    Module.finrank ℝ (Submodule.span ℝ ((fun i j => (A i j : ℝ)) '' ((insert i₀ T : Finset (Fin m)) : Set (Fin m)))) := by
  let rowR : Fin m → (Fin p → ℝ) := fun i j => (A i j : ℝ)
  let S₁ := Submodule.span ℝ (rowR '' (T : Set (Fin m)))
  obtain ⟨B, hB_T, _, hB_span, hker_iff⟩ := row_basis_of_finset A T
  refine Submodule.finrank_lt_finrank_of_lt ?_
  refine lt_of_le_of_ne (Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr (Finset.subset_insert i₀ T)))) ?_
  intro heq
  have hi₀S₁ : rowR i₀ ∈ Submodule.span ℝ (Set.range fun l => rowR (B l)) := by
    change rowR i₀ ∈ Submodule.span ℝ (Set.range fun l => (fun i j => (A i j : ℝ)) (B l))
    rw [hB_span]
    change rowR i₀ ∈ S₁
    dsimp only [S₁]
    rw [heq]
    exact Submodule.subset_span ⟨i₀, Finset.mem_coe.mpr (Finset.mem_insert_self _ _), rfl⟩
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hi₀S₁
  obtain ⟨c, hc_eq⟩ := hi₀S₁
  apply hu0
  have hdot : ((A.map (Int.cast : ℤ → ℝ)) *ᵥ u) i₀ = ∑ j : Fin p, rowR i₀ j * u j := by
    simp [Matrix.mulVec, dotProduct, rowR]
  rw [hdot, ← hc_eq]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hui : ((A.map (Int.cast : ℤ → ℝ)) *ᵥ u) (B l) = 0 := huT _ (hB_T l)
  have hui' : ∑ j : Fin p, rowR (B l) j * u j = 0 := by
    simpa [Matrix.mulVec, dotProduct, rowR] using hui
  calc ∑ j : Fin p, c l * rowR (B l) j * u j
    _ = c l * ∑ j : Fin p, rowR (B l) j * u j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    _ = 0 := by rw [hui', mul_zero]

private lemma filter_pos_sum_eq_sum {p : ℕ} :
    ∀ (xs : List (ℝ × (Fin p → ℝ))),
      (∀ pair ∈ xs, 0 ≤ pair.1) →
      ((xs.filter fun pair => 0 < pair.1).map fun pair => pair.1 • pair.2).sum =
        (xs.map fun pair => pair.1 • pair.2).sum
  | [], _ => by simp
  | hd :: tl, hnn => by
    have hhd := hnn hd List.mem_cons_self
    have htl : ∀ pr ∈ tl, 0 ≤ pr.1 := fun pr hpr => hnn pr (List.mem_cons_of_mem hd hpr)
    by_cases hpos_hd : 0 < hd.1
    · rw [List.filter_cons_of_pos (by simpa using hpos_hd), List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons, filter_pos_sum_eq_sum tl htl]
    · have hhd0 : hd.1 = 0 := le_antisymm (not_lt.mp hpos_hd) hhd
      rw [List.filter_cons_of_neg (by simpa using hpos_hd), List.map_cons, List.sum_cons,
        hhd0, zero_smul, zero_add, filter_pos_sum_eq_sum tl htl]

private lemma caratheodory_cone {p : ℕ} (d : Fin p → ℝ) :
    ∀ (L : List (ℝ × (Fin p → ℝ))),
      (∀ pair ∈ L, 0 < pair.1) →
      d = (L.map fun pair => pair.1 • pair.2).sum →
      ∃ L' : List (ℝ × (Fin p → ℝ)),
        L'.length ≤ p ∧
        (∀ pair ∈ L', pair.2 ∈ L.map Prod.snd) ∧
        (∀ pair ∈ L', 0 < pair.1) ∧
        d = (L'.map fun pair => pair.1 • pair.2).sum := by
  intro L
  have hn : ∀ n : ℕ, ∀ L : List (ℝ × (Fin p → ℝ)), L.length ≤ n →
      (∀ pair ∈ L, 0 < pair.1) →
      d = (L.map fun pair => pair.1 • pair.2).sum →
      ∃ L' : List (ℝ × (Fin p → ℝ)),
        L'.length ≤ p ∧
        (∀ pair ∈ L', pair.2 ∈ L.map Prod.snd) ∧
        (∀ pair ∈ L', 0 < pair.1) ∧
        d = (L'.map fun pair => pair.1 • pair.2).sum := by
    intro n
    induction n with
    | zero =>
      intro L hlen hpos hsum
      exact ⟨L, by omega, fun _ h => List.mem_map_of_mem h, hpos, hsum⟩
    | succ n ih =>
      intro L hlen hpos hsum
      by_cases hp : L.length ≤ p
      · exact ⟨L, hp, fun _ h => List.mem_map_of_mem h, hpos, hsum⟩
      · have hp_lt : p < L.length := Nat.lt_of_not_ge hp
        let m := L.length
        let vec : Fin m → Fin p → ℝ := fun a => (L[a].2)
        let F : (Fin m → ℝ) →ₗ[ℝ] (Fin p → ℝ) :=
          { toFun := fun β => ∑ a : Fin m, β a • vec a
            map_add' := fun u v => by ext j; simp [add_smul, Finset.sum_add_distrib]
            map_smul' := fun r u => by
              ext j; simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by simp only [RingHom.id_apply]; ring }
        have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker F) := by
          have hdim := LinearMap.finrank_range_add_finrank_ker F
          have hr_le : Module.finrank ℝ (LinearMap.range F) ≤ p := by
            simpa [Module.finrank_fin_fun] using Submodule.finrank_le (LinearMap.range F)
          have hm_eq : Module.finrank ℝ (Fin m → ℝ) = m := Module.finrank_fin_fun ℝ
          omega
        have hne : LinearMap.ker F ≠ ⊥ := fun h => by
          rw [h, finrank_bot] at hker_pos; exact lt_irrefl 0 hker_pos
        obtain ⟨β0, hβ0_mem, hβ0_nz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
        have hβ0_sum : ∑ a : Fin m, β0 a • vec a = 0 := hβ0_mem
        let β : Fin m → ℝ := if ∃ a : Fin m, 0 < β0 a then β0 else -β0
        have hβ_sum : ∑ a : Fin m, β a • vec a = 0 := by
          simp only [β]; split_ifs
          · exact hβ0_sum
          · simp [neg_smul, Finset.sum_neg_distrib, hβ0_sum]
        have hβ_pos : ∃ a : Fin m, 0 < β a := by
          simp only [β]; split_ifs with h
          · exact h
          · obtain ⟨a₀, ha₀⟩ := show ∃ a₀ : Fin m, β0 a₀ ≠ 0 from by
              by_contra hnone; push Not at hnone; exact hβ0_nz (funext hnone)
            push Not at h
            exact ⟨a₀, neg_pos.mpr (lt_of_le_of_ne (h a₀) ha₀)⟩
        let Ip := Finset.univ.filter fun a : Fin m => 0 < β a
        have hIp_ne : Ip.Nonempty := by
          obtain ⟨a₀, ha₀⟩ := hβ_pos
          exact ⟨a₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha₀⟩⟩
        let t := Ip.inf' hIp_ne fun a => L[a].1 / β a
        obtain ⟨a_min, ha_min_mem, ha_min_eq⟩ := Finset.exists_mem_eq_inf' hIp_ne fun a => L[a].1 / β a
        have hLa_pos : 0 < L[a_min].1 := hpos _ (List.getElem_mem _)
        have hβa_pos : 0 < β a_min := (Finset.mem_filter.mp ha_min_mem).2
        have ht_pos : 0 < t := by dsimp only [t]; rw [ha_min_eq]; exact div_pos hLa_pos hβa_pos
        let pairs : List (ℝ × (Fin p → ℝ)) :=
          List.ofFn fun a : Fin m => (L[a].1 - t * β a, vec a)
        let L1 := pairs.filter fun pair => 0 < pair.1
        have hpairs_sum : (pairs.map fun pair => pair.1 • pair.2).sum = d := by
          rw [hsum]
          have hL_ofFn : L = List.ofFn fun a : Fin m => L[a] := List.ofFn_getElem.symm
          have h1 : (pairs.map fun pair => pair.1 • pair.2).sum =
              ∑ a : Fin m, (L[a].1 - t * β a) • vec a := by
            simp only [pairs, List.map_ofFn, Function.comp_def, List.sum_ofFn]
          have h2 : (L.map fun pair => pair.1 • pair.2).sum = ∑ a : Fin m, L[a].1 • vec a := by
            conv_lhs => rw [hL_ofFn]
            simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn, vec]
          rw [h1, h2]
          have hsub : ∀ a : Fin m, (L[a].1 - t * β a) • vec a = L[a].1 • vec a - t • (β a • vec a) :=
            fun a => by rw [sub_smul, smul_smul]
          calc ∑ a : Fin m, (L[a].1 - t * β a) • vec a
            _ = ∑ a : Fin m, (L[a].1 • vec a - t • (β a • vec a)) :=
                Finset.sum_congr rfl fun a _ => hsub a
            _ = (∑ a : Fin m, L[a].1 • vec a) - t • ∑ a : Fin m, β a • vec a := by
                rw [Finset.sum_sub_distrib, ← Finset.smul_sum]
            _ = ∑ a : Fin m, L[a].1 • vec a := by rw [hβ_sum, smul_zero, sub_zero]
        have hpairs_nn : ∀ pair ∈ pairs, 0 ≤ pair.1 := by
          intro pair hp_mem
          rw [List.mem_ofFn] at hp_mem
          obtain ⟨a, rfl⟩ := hp_mem
          by_cases hβa : 0 < β a
          · have hle : t ≤ L[a].1 / β a :=
              Finset.inf'_le (f := fun a => L[a].1 / β a) (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hβa⟩)
            have := (le_div_iff₀ hβa).mp hle
            linarith
          · push Not at hβa
            have hLa : 0 < L[a].1 := hpos _ (List.getElem_mem _)
            nlinarith
        have hL1_sum : d = (L1.map fun pair => pair.1 • pair.2).sum := by
          dsimp only [L1]
          rw [filter_pos_sum_eq_sum pairs hpairs_nn, hpairs_sum]
        have hL1_len : L1.length ≤ n := by
          have hle_lt : L1.length < pairs.length := by
            refine List.length_filter_lt_length_iff_exists.mpr ⟨(L[a_min].1 - t * β a_min, vec a_min), ?_, ?_⟩
            · rw [List.mem_ofFn]; exact ⟨a_min, rfl⟩
            · have hzero : L[a_min].1 - t * β a_min = 0 := by
                dsimp only [t]; rw [ha_min_eq, div_mul_cancel₀ _ hβa_pos.ne', sub_self]
              simp only [decide_eq_true_eq, not_lt, decide_eq_false_iff_not]; exact hzero.le
          have hp_len : pairs.length = m := by simp [pairs]
          omega
        have hL1_pos : ∀ pair ∈ L1, 0 < pair.1 := fun pair hp_mem => by
          simpa using (List.mem_filter.mp hp_mem).2
        obtain ⟨L', hL'_len, hL'_snd, hL'_pos, hL'_sum⟩ := ih L1 hL1_len hL1_pos hL1_sum
        refine ⟨L', hL'_len, fun pair hp_mem => ?_, hL'_pos, hL'_sum⟩
        have hsnd := hL'_snd pair hp_mem
        rw [List.mem_map] at hsnd
        obtain ⟨q, hq_L1, hq_eq⟩ := hsnd
        have hq_pairs := (List.mem_filter.mp hq_L1).1
        rw [List.mem_ofFn] at hq_pairs
        obtain ⟨a, ha_eq⟩ := hq_pairs
        rw [← hq_eq, ← ha_eq]
        exact List.mem_map.mpr ⟨L[a], List.getElem_mem _, rfl⟩
  exact hn L.length L le_rfl

private lemma smulList {α : Type} {p : ℕ} (w : ℝ) (f : α → Fin p → ℝ) (l : List α) :
    (l.map fun x => w • f x).sum = w • (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [smul_add,ih]

set_option maxHeartbeats 2000000 in
private lemma cone_decomp_rays {mB p H : ℕ} (hp : 1 ≤ p) (hH1 : 1 ≤ H)
    (B : Matrix (Fin mB) (Fin p) ℤ) (hB : ∀ i j, |B i j| ≤ (H : ℤ))
    (φ : (Fin p → ℝ) →ₗ[ℝ] ℝ)
    (hφ_nn : ∀ y : Fin p → ℝ, (∀ i, ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y) i ≤ 0) → 0 ≤ φ y)
    (hφ_zero : ∀ y : Fin p → ℝ, (∀ i, ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y) i ≤ 0) → φ y = 0 → y = 0) :
    ∀ k : ℕ, ∀ y : Fin p → ℝ,
      (p - 1) - tightRank B (fun _ => 0) y ≤ k →
      (∀ i, ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y) i ≤ 0) →
      y ≠ 0 →
      ∃ L : List (ℝ × (Fin p → ℤ)),
        (∀ pair ∈ L, 0 < pair.1) ∧
        (∀ pair ∈ L, ∀ i, ((B.map (Int.cast : ℤ → ℝ)) *ᵥ fun j => (pair.2 j : ℝ)) i ≤ 0) ∧
        (∀ pair ∈ L, pair.2 ≠ 0) ∧
        (∀ pair ∈ L, ∀ j, |pair.2 j| ≤ (((p - 1).factorial * H ^ (p - 1) : ℕ) : ℤ)) ∧
        y = (L.map fun pair => pair.1 • (fun j => (pair.2 j : ℝ))).sum := by
  let _ := hH1
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro y hk hy_feas hy_nz
    let T := tightRows B (fun _ => 0) y
    have hφy_pos : 0 < φ y :=
      lt_of_le_of_ne (hφ_nn y hy_feas) fun h0 => hy_nz (hφ_zero y hy_feas h0.symm)
    obtain ⟨B_sub, hB_T, hB_indep, _, hker_iff⟩ := row_basis_of_finset B T
    let rk := tightRank B (fun _ => 0) y
    have hrk_orth : ∀ l : Fin rk, ∑ j : Fin p, y j * (B (B_sub l) j : ℝ) = 0 := by
      intro l
      have hl := (Finset.mem_filter.mp (hB_T l)).2
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.cast_zero] at hl
      calc ∑ j : Fin p, y j * (B (B_sub l) j : ℝ)
        _ = ∑ j : Fin p, (B (B_sub l) j : ℝ) * y j := Finset.sum_congr rfl fun _ _ => mul_comm _ _
        _ = 0 := hl
    have hrk_le_p1 : rk ≤ p - 1 := by
      let vecs : Fin (rk + 1) → (Fin p → ℝ) :=
        Fin.cases y (fun l : Fin rk => fun j : Fin p => (B (B_sub l) j : ℝ))
      have hvis : LinearIndependent ℝ vecs := by
        rw [Fintype.linearIndependent_iff]
        intro α hα
        have hdot : ∑ j : Fin p, y j * (∑ r : Fin (rk + 1), α r * vecs r j) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          have hj := congrFun hα j
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
          rw [hj, mul_zero]
        simp_rw [Finset.mul_sum] at hdot
        rw [Finset.sum_comm] at hdot
        have hdot2 : ∑ r : Fin (rk + 1), α r * (∑ j : Fin p, y j * vecs r j) = 0 := by
          rw [← hdot]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [Fin.sum_univ_succ] at hdot2
        have hrest0 : ∑ l : Fin rk, α l.succ * (∑ j : Fin p, y j * vecs l.succ j) = 0 := by
          refine Finset.sum_eq_zero fun l _ => ?_
          simp only [vecs, Fin.cases_succ]
          rw [hrk_orth l, mul_zero]
        rw [hrest0, add_zero] at hdot2
        have hysq : 0 < ∑ j : Fin p, y j * vecs 0 j := by
          obtain ⟨j₀, hj₀⟩ := show ∃ j₀ : Fin p, y j₀ ≠ 0 from by
            by_contra hnone; push Not at hnone; exact hy_nz (funext hnone)
          simp only [vecs, Fin.cases_zero]
          exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
            ⟨j₀, Finset.mem_univ j₀, mul_self_pos.mpr hj₀⟩
        have hα0 : α 0 = 0 := (mul_eq_zero.mp hdot2).resolve_right hysq.ne'
        have htail : ∑ l : Fin rk, α l.succ • (fun j : Fin p => (B (B_sub l) j : ℝ)) = 0 := by
          ext j
          have hj := congrFun hα j
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
          rw [Fin.sum_univ_succ, hα0, zero_mul, zero_add] at hj
          simpa [vecs] using hj
        exact Fin.cases hα0 ((Fintype.linearIndependent_iff.mp hB_indep) _ htail)
      have hcard_le : rk + 1 ≤ p := by
        simpa [Module.finrank_fin_fun] using hvis.fintype_card_le_finrank
      omega
    by_cases hbase : rk = p - 1
    · have hp_eq : p = (p - 1) + 1 := by omega
      let e_pq : Fin ((p - 1) + 1) ≃ Fin p := finCongr hp_eq.symm
      let e_rk : Fin (p - 1) ≃ Fin rk := finCongr hbase.symm
      let F : Matrix (Fin ((p - 1) + 1)) (Fin (p - 1)) ℤ :=
        Matrix.of fun a l => B (B_sub (e_rk l)) (e_pq a)
      let y_f : Fin ((p - 1) + 1) → ℝ := y ∘ e_pq
      have hy_f_nz : y_f ≠ 0 := fun hz => hy_nz (funext fun j => by
        have := congrFun hz (e_pq.symm j); simpa [y_f] using this)
      have hF_indep : LinearIndependent ℝ (fun l : Fin (p - 1) => fun a : Fin ((p - 1) + 1) => (F a l : ℝ)) := by
        rw [Fintype.linearIndependent_iff]
        intro α hα
        have hcomp := (hB_indep.comp e_rk e_rk.injective)
        refine Fintype.linearIndependent_iff.mp hcomp α ?_
        ext j
        have ha := congrFun hα (e_pq.symm j)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp_apply]
        change (∑ l, α l * (B (B_sub (e_rk l)) j : ℝ)) = 0
        simpa [F] using ha
      have hy_f_orth : ∀ l : Fin (p - 1), ∑ a : Fin ((p - 1) + 1), y_f a * (F a l : ℝ) = 0 := by
        intro l
        rw [← hrk_orth (e_rk l)]
        exact e_pq.sum_comp (fun j => y j * (B (B_sub (e_rk l)) j : ℝ))
      obtain ⟨hcf0, _, α, hα0, hα⟩ := cofactorVec_proportional_of_orth F hF_indep y_f hy_f_nz hy_f_orth
      let sgn : ℤ := if 0 < α then 1 else -1
      let v : Fin p → ℤ := fun j => sgn * cofactorVec F (e_pq.symm j)
      let c : ℝ := |(α : ℝ)|⁻¹
      have hc_pos : 0 < c := inv_pos.mpr (abs_pos.mpr hα0)
      have hy_eq_cv : ∀ j : Fin p, y j = c * (v j : ℝ) := by
        intro j
        have ha := congrFun hα (e_pq.symm j)
        simp only [y_f, Function.comp_apply, Equiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul] at ha
        rcases lt_or_gt_of_ne hα0 with hlt | hgt
        · have hsgn : sgn = -1 := by simp [sgn, hlt.not_gt]
          have hc_eq : c = (-α)⁻¹ := by simp only [c, abs_of_neg hlt]
          simp only [v, hsgn, Int.cast_mul, Int.cast_neg, Int.cast_one, ha, hc_eq]
          field_simp [hlt.ne]
        · have hsgn : sgn = 1 := by simp [sgn, hgt]
          have hc_eq : c = α⁻¹ := by simp only [c, abs_of_pos hgt]
          simp only [v, hsgn, Int.cast_mul, Int.cast_one, ha, hc_eq]
          field_simp [hgt.ne']
      refine ⟨[(c, v)], ?_, ?_, ?_, ?_, ?_⟩
      · intro pair hp_mem; simp only [List.mem_singleton] at hp_mem; subst hp_mem; exact hc_pos
      · intro pair hp_mem i
        simp only [List.mem_singleton] at hp_mem; subst hp_mem
        have hv_eq : (fun j : Fin p => (v j : ℝ)) = c⁻¹ • y := by
          ext j; simp only [Pi.smul_apply, smul_eq_mul, hy_eq_cv j]; rw [inv_mul_cancel_left₀ hc_pos.ne']
        rw [hv_eq, Matrix.mulVec_smul]
        exact smul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc_pos.le) (hy_feas i)
      · intro pair hp_mem hv0
        simp only [List.mem_singleton] at hp_mem; subst hp_mem
        apply hcf0
        ext a
        have hva := congrFun hv0 (e_pq a)
        simp only [v, Pi.zero_apply, Equiv.symm_apply_apply, mul_eq_zero] at hva
        rcases hva with hs0 | h0
        · simp only [sgn] at hs0; split_ifs at hs0 <;> omega
        · exact h0
      · intro pair hp_mem j
        simp only [List.mem_singleton] at hp_mem; subst hp_mem
        have hsgn_abs : |sgn| = 1 := by simp only [sgn]; split_ifs <;> simp
        simp only [v, abs_mul, hsgn_abs, one_mul]
        exact cofactorVec_bound F H (fun _ _ => hB _ _) _
      · ext j
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          Pi.smul_apply, smul_eq_mul]
        exact hy_eq_cv j
    · have hrk_lt : rk < p - 1 := lt_of_le_of_ne hrk_le_p1 hbase
      let L_B : (Fin p → ℝ) →ₗ[ℝ] (Fin rk → ℝ) :=
        { toFun := fun u l => ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u) (B_sub l)
          map_add' := fun u v => by ext l; simp [Matrix.mulVec_add]
          map_smul' := fun r u => by ext l; simp [Matrix.mulVec_smul] }
      have hy_ker : y ∈ LinearMap.ker L_B := by
        ext l
        change ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y) (B_sub l) = 0
        simpa using (Finset.mem_filter.mp (hB_T l)).2
      have hker_gt : 1 < Module.finrank ℝ (LinearMap.ker L_B) := by
        have hdim := LinearMap.finrank_range_add_finrank_ker L_B
        have hr_le : Module.finrank ℝ (LinearMap.range L_B) ≤ rk := by
          simpa [Module.finrank_fin_fun] using Submodule.finrank_le (LinearMap.range L_B)
        have hp_eq : Module.finrank ℝ (Fin p → ℝ) = p := Module.finrank_fin_fun ℝ
        omega
      let y_ker : LinearMap.ker L_B := ⟨y, hy_ker⟩
      have hy_indep : LinearIndependent ℝ (fun _ : Fin 1 => y_ker) := by
        rw [linearIndependent_unique_iff]
        intro hz
        exact hy_nz (congrArg Subtype.val hz)
      obtain ⟨u_ker, hu_indep⟩ := exists_linearIndependent_snoc_of_lt_finrank hy_indep hker_gt
      let u0 : Fin p → ℝ := u_ker.1
      let u' : Fin p → ℝ := φ y • u0 - φ u0 • y
      have hu'_ker : u' ∈ LinearMap.ker L_B := Submodule.sub_mem _
        (Submodule.smul_mem _ _ u_ker.2) (Submodule.smul_mem _ _ hy_ker)
      have hu'_T : ∀ i ∈ T, ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i = 0 :=
        (hker_iff u').mp fun l => congrFun hu'_ker l
      have hu'_nz : u' ≠ 0 := by
        intro hz
        have h_ker_eq : (φ y) • u_ker - (φ u0) • y_ker = 0 := Subtype.ext hz
        have hlin : (-(φ u0)) • y_ker + (φ y) • u_ker = 0 := by
          calc (-(φ u0)) • y_ker + (φ y) • u_ker
            _ = (φ y) • u_ker - (φ u0) • y_ker := by
              apply Subtype.ext
              change (-(φ u0)) • y + (φ y) • u0 = (φ y) • u0 - (φ u0) • y
              rw [neg_smul, sub_eq_add_neg, add_comm]
            _ = 0 := h_ker_eq
        have hbad := (Fintype.linearIndependent_iff.mp hu_indep) ![-(φ u0), φ y] (by
          rw [Fin.sum_univ_two]
          change (-φ u0) • y_ker + φ y • u_ker = 0
          exact hlin)
        have h1 := hbad 1
        simp [hφy_pos.ne'] at h1
      have hφ_u' : φ u' = 0 := by
        simp [u', map_sub, map_smul, smul_eq_mul, mul_comm]
      have hex_pos : ∃ i₁ : Fin mB, 0 < ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i₁ := by
        by_contra hnone; push Not at hnone
        exact hu'_nz (hφ_zero u' hnone hφ_u')
      have hex_neg : ∃ i₂ : Fin mB, ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i₂ < 0 := by
        by_contra hnone; push Not at hnone
        have hneg_feas : ∀ i, ((B.map (Int.cast : ℤ → ℝ)) *ᵥ (-u')) i ≤ 0 := fun i => by
          simp [Matrix.mulVec_neg]; exact hnone i
        have hneg0 := hφ_zero (-u') hneg_feas (by simp [map_neg, hφ_u'])
        exact hu'_nz (neg_eq_zero.mp hneg0)
      obtain ⟨i₁, hi₁⟩ := hex_pos
      obtain ⟨i₂, hi₂⟩ := hex_neg
      let Ip := Finset.univ.filter fun i => 0 < ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i
      let Im := Finset.univ.filter fun i => ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i < 0
      have hIp_ne : Ip.Nonempty := ⟨i₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₁⟩⟩
      have hIm_ne : Im.Nonempty := ⟨i₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₂⟩⟩
      let r1 : Fin mB → ℝ := fun i => (-((B.map (Int.cast : ℤ → ℝ)) *ᵥ y) i) / ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i
      let r2 : Fin mB → ℝ := fun i => (((B.map (Int.cast : ℤ → ℝ)) *ᵥ y) i) / ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i
      let t1 := Ip.inf' hIp_ne r1
      let t2 := Im.inf' hIm_ne r2
      obtain ⟨j1, hj1_mem, hj1_eq⟩ := Finset.exists_mem_eq_inf' hIp_ne r1
      obtain ⟨j2, hj2_mem, hj2_eq⟩ := Finset.exists_mem_eq_inf' hIm_ne r2
      have hu'_j1 : 0 < ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') j1 := (Finset.mem_filter.mp hj1_mem).2
      have hu'_j2 : ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') j2 < 0 := (Finset.mem_filter.mp hj2_mem).2
      have hj1_not_T : j1 ∉ T := fun hjT => (hu'_T j1 hjT ▸ hu'_j1).false
      have hj2_not_T : j2 ∉ T := fun hjT => (hu'_T j2 hjT ▸ hu'_j2).false
      have hy_j1_lt : ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y) j1 < 0 := by
        refine lt_of_le_of_ne (hy_feas j1) fun heq => hj1_not_T ?_
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using heq⟩
      have hy_j2_lt : ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y) j2 < 0 := by
        refine lt_of_le_of_ne (hy_feas j2) fun heq => hj2_not_T ?_
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using heq⟩
      have ht1_pos : 0 < t1 := by dsimp only [t1]; rw [hj1_eq]; exact div_pos (neg_pos.mpr hy_j1_lt) hu'_j1
      have ht2_pos : 0 < t2 := by dsimp only [t2]; rw [hj2_eq]; exact div_pos_of_neg_of_neg hy_j2_lt hu'_j2
      let y1 := y + t1 • u'
      let y2 := y - t2 • u'
      have hy1_feas : ∀ i, ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y1) i ≤ 0 := by
        intro i
        have hmul : ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y1) i =
            ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y) i + t1 * ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i := by
          simp [y1, Matrix.mulVec_add, Matrix.mulVec_smul]
        rw [hmul]
        by_cases hi : 0 < ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i
        · have hle : t1 ≤ r1 i := Finset.inf'_le (f := r1) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
          have := (le_div_iff₀ hi).mp hle
          linarith
        · push Not at hi
          have h0 := hy_feas i
          nlinarith
      have hy2_feas : ∀ i, ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y2) i ≤ 0 := by
        intro i
        have hmul : ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y2) i =
            ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y) i - t2 * ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i := by
          simp [y2, Matrix.mulVec_sub, Matrix.mulVec_smul]
        rw [hmul]
        by_cases hi : ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i < 0
        · have hle : t2 ≤ r2 i := Finset.inf'_le (f := r2) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
          have := (le_div_iff_of_neg hi).mp hle
          linarith
        · push Not at hi
          have h0 := hy_feas i
          nlinarith
      have hy1_nz : y1 ≠ 0 := fun h0 => by
        have hφ1 : φ y1 = φ y := by simp [y1, map_add, map_smul, hφ_u']
        rw [h0, map_zero] at hφ1
        linarith
      have hy2_nz : y2 ≠ 0 := fun h0 => by
        have hφ2 : φ y2 = φ y := by simp [y2, map_sub, map_smul, hφ_u']
        rw [h0, map_zero] at hφ2
        linarith
      have hT_sub1 : insert j1 T ⊆ tightRows B (fun _ => 0) y1 := by
        intro i hi
        dsimp only [tightRows]
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hmul : ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y1) i =
            ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y) i + t1 * ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i := by
          simp [y1, Matrix.mulVec_add, Matrix.mulVec_smul]
        rw [hmul, Int.cast_zero]
        rcases Finset.mem_insert.mp hi with rfl | hiT
        · dsimp only [t1]; rw [hj1_eq]; simp only [r1]; rw [div_mul_cancel₀ _ hu'_j1.ne']; ring
        · have hyi := (Finset.mem_filter.mp hiT).2
          simp only [Int.cast_zero] at hyi
          rw [hyi, hu'_T i hiT, mul_zero, add_zero]
      have hT_sub2 : insert j2 T ⊆ tightRows B (fun _ => 0) y2 := by
        intro i hi
        dsimp only [tightRows]
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hmul : ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y2) i =
            ((B.map (Int.cast : ℤ → ℝ)) *ᵥ y) i - t2 * ((B.map (Int.cast : ℤ → ℝ)) *ᵥ u') i := by
          simp [y2, Matrix.mulVec_sub, Matrix.mulVec_smul]
        rw [hmul, Int.cast_zero]
        rcases Finset.mem_insert.mp hi with rfl | hiT
        · dsimp only [t2]; rw [hj2_eq]; simp only [r2]; rw [div_mul_cancel₀ _ hu'_j2.ne]; ring
        · have hyi := (Finset.mem_filter.mp hiT).2
          simp only [Int.cast_zero] at hyi
          rw [hyi, hu'_T i hiT, mul_zero, sub_zero]
      have hrk1_lt : rk < tightRank B (fun _ => 0) y1 := lt_of_lt_of_le
        (tightRank_lt_insert B T j1 u' hu'_T hu'_j1.ne')
        (Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hT_sub1))))
      have hrk2_lt : rk < tightRank B (fun _ => 0) y2 := lt_of_lt_of_le
        (tightRank_lt_insert B T j2 u' hu'_T hu'_j2.ne)
        (Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hT_sub2))))
      have hk1_lt : (p - 1) - tightRank B (fun _ => 0) y1 < k := by omega
      have hk2_lt : (p - 1) - tightRank B (fun _ => 0) y2 < k := by omega
      obtain ⟨L1, hL1_pos, hL1_feas, hL1_nz, hL1_bd, hL1_sum⟩ :=
        ih _ hk1_lt y1 le_rfl hy1_feas hy1_nz
      obtain ⟨L2, hL2_pos, hL2_feas, hL2_nz, hL2_bd, hL2_sum⟩ :=
        ih _ hk2_lt y2 le_rfl hy2_feas hy2_nz
      let den := t1 + t2
      have hden_pos : 0 < den := add_pos ht1_pos ht2_pos
      let w1 := t2 / den
      let w2 := t1 / den
      have hw1_pos : 0 < w1 := div_pos ht2_pos hden_pos
      have hw2_pos : 0 < w2 := div_pos ht1_pos hden_pos
      let L := (L1.map fun pr => (w1 * pr.1, pr.2)) ++ (L2.map fun pr => (w2 * pr.1, pr.2))
      refine ⟨L, ?_, ?_, ?_, ?_, ?_⟩
      · intro pair hp_mem
        rcases List.mem_append.mp hp_mem with h1 | h2
        · obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp h1
          exact mul_pos hw1_pos (hL1_pos pr hpr)
        · obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp h2
          exact mul_pos hw2_pos (hL2_pos pr hpr)
      · intro pair hp_mem i
        rcases List.mem_append.mp hp_mem with h1 | h2
        · obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp h1; exact hL1_feas pr hpr i
        · obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp h2; exact hL2_feas pr hpr i
      · intro pair hp_mem
        rcases List.mem_append.mp hp_mem with h1 | h2
        · obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp h1; exact hL1_nz pr hpr
        · obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp h2; exact hL2_nz pr hpr
      · intro pair hp_mem j
        rcases List.mem_append.mp hp_mem with h1 | h2
        · obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp h1; exact hL1_bd pr hpr j
        · obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp h2; exact hL2_bd pr hpr j
      · have hy_comb : y = w1 • y1 + w2 • y2 := by
          ext j
          simp only [y1, y2, w1, w2, den, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          field_simp [hden_pos.ne']
          ring
        have hmap1 : ((L1.map fun pr => (w1 * pr.1, pr.2)).map fun pr => pr.1 • fun j => (pr.2 j : ℝ)).sum =
            w1 • y1 := by
          rw [hL1_sum, List.map_map]
          have heq : ((fun pr : ℝ × (Fin p → ℤ) => (w1 * pr.1) • (fun j => (pr.2 j : ℝ))) =
              fun pr => w1 • (pr.1 • (fun j => (pr.2 j : ℝ)))) := by
            ext pr j; simp [smul_eq_mul, mul_assoc]
          simp_rw [Function.comp_def, heq]
          exact smulList w1 (fun (pr : ℝ × (Fin p → ℤ)) => pr.1 • fun j => (pr.2 j : ℝ)) L1
        have hmap2 : ((L2.map fun pr => (w2 * pr.1, pr.2)).map fun pr => pr.1 • fun j => (pr.2 j : ℝ)).sum =
            w2 • y2 := by
          rw [hL2_sum, List.map_map]
          have heq : ((fun pr : ℝ × (Fin p → ℤ) => (w2 * pr.1) • (fun j => (pr.2 j : ℝ))) =
              fun pr => w2 • (pr.1 • (fun j => (pr.2 j : ℝ)))) := by
            ext pr j; simp [smul_eq_mul, mul_assoc]
          simp_rw [Function.comp_def, heq]
          exact smulList w2 (fun (pr : ℝ × (Fin p → ℤ)) => pr.1 • fun j => (pr.2 j : ℝ)) L2
        simp only [L, List.map_append, List.sum_append, hmap1, hmap2, ← hy_comb]


private abbrev Good {p m : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
    (x : Fin (p+1) → ℝ) := (∀ j, 0 ≤ x j) ∧
      ∀ i, (∑ j, (A i j : ℝ) * x j.succ) ≤ (b i : ℝ) * x 0

private def aug {p m : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ) :
    Matrix (Fin (m+(p+1))) (Fin (p+1)) ℤ :=
  Matrix.of (Fin.addCases (fun i => Fin.cons (-b i) (A i))
    (fun j l => if j = l then -1 else 0))

private lemma aug_spec {p m : ℕ} (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
    (x : Fin (p+1) → ℝ) :
    (∀ i, (((aug A b).map (Int.cast : ℤ → ℝ)) *ᵥ x) i ≤ 0) ↔ Good A b x := by
  have hleft (i : Fin m) : (((aug A b).map (Int.cast : ℤ → ℝ)) *ᵥ x) (Fin.castAdd _ i) =
      -(b i : ℝ) * x 0 + ∑ j, (A i j : ℝ) * x j.succ := by
    simp [aug,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  have hright (i : Fin (p+1)) : (((aug A b).map (Int.cast : ℤ → ℝ)) *ᵥ x) (Fin.natAdd m i) = -x i := by
    simp [aug,Matrix.mulVec,dotProduct,ite_mul]
  constructor
  · intro h
    exact ⟨fun i => by have := h (Fin.natAdd m i); rw [hright] at this; linarith,
      fun i => by have := h (Fin.castAdd _ i); rw [hleft] at this; linarith⟩
  · rintro ⟨hn,h⟩
    apply Fin.addCases
    · intro i; rw [hleft]; linarith [h i]
    · intro i; rw [hright]; linarith [hn i]

private lemma good_sum {p m : ℕ} {A : Matrix (Fin m) (Fin p) ℤ} {b : Fin m → ℤ}
    {ι : Type} [Fintype ι] (a : ι → ℝ) (x : ι → Fin (p+1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, Good A b (x i)) :
    Good A b (∑ i, a i • x i) := by
  constructor
  · intro j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (ha i) ((hx i).1 j)
  intro l
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro i _
  calc
    _ = a i * ∑ j, (A l j : ℝ) * x i j.succ := by simp [Finset.mul_sum,mul_left_comm]
    _ ≤ a i * ((b l : ℝ) * x i 0) := mul_le_mul_of_nonneg_left ((hx i).2 l) (ha i)
    _ = _ := by ring

private lemma sparse_rays {p m H : ℕ} (hH : 1 ≤ H)
    (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hb : ∀ i, |b i| ≤ (H : ℤ))
    (w : Fin (p+1) → ℝ) (hw : Good A b w) (hw0 : w ≠ 0) :
    ∃ (n : ℕ) (a : Fin n → ℝ) (v : Fin n → Fin (p+1) → ℤ),
      n ≤ p+1 ∧ (∀ i, 0 < a i) ∧ (∀ i, v i ≠ 0) ∧
      (∀ i, Good A b (fun j => (v i j : ℝ))) ∧
      (∀ i j, |v i j| ≤ ((p.factorial * H^p : ℕ) : ℤ)) ∧
      w = ∑ i, a i • (fun j => (v i j : ℝ)) := by
  classical
  let φ : (Fin (p+1) → ℝ) →ₗ[ℝ] ℝ := ∑ j, LinearMap.proj j
  have hφ (y : Fin (p+1) → ℝ) : φ y = ∑ j, y j := by simp [φ]
  have hcoeff : ∀ i j, |aug A b i j| ≤ H := by
    apply Fin.addCases
    · intro i; apply Fin.cases
      · simpa [aug] using hb i
      · intro j; simpa [aug] using hA i j
    · intro i j; by_cases h : i=j <;> simp [aug,h,hH]
  obtain ⟨L,ha,hv,hnz,hvB,hsum⟩ :=
    cone_decomp_rays (Nat.succ_pos _) hH (aug A b) hcoeff φ
      (fun y hy => by rw [hφ]; exact Finset.sum_nonneg fun j _ => ((aug_spec A b y).mp hy).1 j)
      (fun y hy h0 => by
        rw [hφ] at h0
        have hn := ((aug_spec A b y).mp hy).1
        exact funext fun j => (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp h0 j (Finset.mem_univ j))
      p w (by omega) ((aug_spec A b w).mpr hw) hw0
  let castPair := fun q : ℝ × (Fin (p+1) → ℤ) => (q.1, fun j => (q.2 j : ℝ))
  obtain ⟨K,hlen,hmem,hpos,hrep⟩ := caratheodory_cone w (L.map castPair)
    (fun q hq => by obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hq; exact ha _ hl)
    (by simpa [List.map_map,castPair,Function.comp_def] using hsum)
  have hx (i : Fin K.length) : ∃ q ∈ L, (fun j => (q.2 j : ℝ)) = K[i].2 := by
    have h := hmem K[i] (List.getElem_mem ..)
    simpa [List.mem_map,List.map_map,castPair,Function.comp_def] using h
  choose q hq hqe using hx
  refine ⟨K.length,fun i => K[i].1,fun i => (q i).2,hlen,fun i => hpos _ (List.getElem_mem ..),
    fun i => hnz _ (hq i),fun i => (aug_spec ..).mp (hv _ (hq i)),fun i j => ?_,?_⟩
  · simpa using hvB _ (hq i) j
  · rw [hrep]; simp_rw [hqe]
    rw [← Fin.sum_ofFn]; congr 1
    exact List.ext_getElem (by simp) (by simp)

end IntConeFPT.Recession

open IntConeFPT.Recession

theorem solution {p m H : ℕ} (hp : 1 ≤ p) (hH : 1 ≤ H)
    (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ H) (hb : ∀ i, |b i| ≤ H)
    (z : Fin p → ℕ) (hz : ∀ i, ∑ j, A i j * (z j : ℤ) ≤ b i)
    (hlarge : p * (p + 1) * p.factorial * H ^ p < ∑ j, z j) :
    ∃ y r : Fin p → ℕ, z = y + r ∧
      (∀ i, ∑ j, A i j * (y j : ℤ) ≤ b i) ∧
      (∀ i, ∑ j, A i j * (r j : ℤ) ≤ 0) ∧
      0 < ∑ j, r j ∧ ∑ j, r j ≤ p * (p + 1) * p.factorial * H ^ p := by
  classical
  let w : Fin (p+1) → ℝ := Fin.cons 1 (fun j => (z j : ℝ))
  have hw : Good A b w := by
    constructor
    · apply Fin.cases <;> simp [w]
    · intro i; simp [w]; exact_mod_cast hz i
  obtain ⟨n,a,v,hn,ha,hne,hgood,hbound,hrep⟩ := sparse_rays hH A b hA hb w hw
    (fun he => by have := congrFun he 0; simp [w] at this)
  let D := p.factorial * H^p
  have hvpos (i : Fin n) (j) : 0 ≤ v i j := by
    have h : (0 : ℝ) ≤ (v i j : ℝ) := (hgood i).1 j
    exact_mod_cast h
  have hwj (j) : w j = ∑ i, a i * (v i j : ℝ) := by simpa using congrFun hrep j
  obtain ⟨k,hk⟩ : ∃ k, 1 < a k := by
    by_contra! he
    have upper (j : Fin p) : (z j : ℝ) ≤ (n : ℝ) * D := by
      calc
        _ = _ := hwj j.succ
        _ ≤ ∑ _ : Fin n, (D : ℝ) := Finset.sum_le_sum fun i _ => by
          have h1 : (v i j.succ : ℝ) ≤ D := by exact_mod_cast (le_abs_self _).trans (hbound i j.succ)
          exact (mul_le_of_le_one_left (by exact_mod_cast hvpos i j.succ) (he i)).trans h1
        _ = _ := by simp
    have hs : ∑ j, z j ≤ p * (p+1) * p.factorial * H^p := by
      calc
        _ ≤ ∑ _ : Fin p, n*D := Finset.sum_le_sum fun j _ => by exact_mod_cast upper j
        _ = p * n * D := by simp [mul_assoc]
        _ ≤ p * (p+1) * D := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left p hn)
        _ = _ := by dsimp [D]; ring
    omega
  have hterm (j) : a k * (v k j : ℝ) ≤ w j := by
    rw [hwj]
    exact Finset.single_le_sum (fun i _ => mul_nonneg (ha i).le ((hgood i).1 j)) (Finset.mem_univ k)
  have hk0 : v k 0 = 0 := by
    by_contra h
    have h1 : (1 : ℝ) ≤ v k 0 := by exact_mod_cast (show 1 ≤ v k 0 by have := hvpos k 0; omega)
    have hle := le_mul_of_one_le_right (ha k).le h1
    have := hterm 0
    simp [w] at this; linarith
  let r := fun j : Fin p => (v k j.succ).toNat
  have hr (j) : (r j : ℤ) = v k j.succ := Int.toNat_of_nonneg (hvpos ..)
  have hrle (j) : r j ≤ z j := by
    have hl := (le_mul_of_one_le_left ((hgood k).1 j.succ) hk.le).trans (hterm j.succ)
    change (v k j.succ : ℝ) ≤ (z j : ℝ) at hl
    exact_mod_cast (hr j).le.trans (by exact_mod_cast hl : v k j.succ ≤ (z j : ℤ))
  let y := fun j => z j - r j
  have hzy : z = y+r := funext fun j => Nat.sub_add_cancel (hrle j) |>.symm
  have hrr (j) : (r j : ℝ) = (v k j.succ : ℝ) := by exact_mod_cast hr j
  let u := fun j => (v k j : ℝ)
  let θ := Function.update a k (a k - 1)
  have hθ (i) : 0 ≤ θ i := by by_cases he : i=k <;> simp [θ,he, hk.le, (ha i).le]
  have hrest : Good A b (w-u) := by
    have he : w-u = ∑ i, θ i • (fun j => (v i j : ℝ)) := by
      rw [hrep]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
          ← Finset.sum_erase_add _ (fun i => θ i • _) (Finset.mem_univ k)]
      have hrst : (∑ i ∈ Finset.univ.erase k, θ i • fun j => (v i j : ℝ)) =
          ∑ i ∈ Finset.univ.erase k, a i • fun j => (v i j : ℝ) := by
        apply Finset.sum_congr rfl; intro i hi
        rw [show θ i = a i from Function.update_of_ne (Finset.ne_of_mem_erase hi) ..]
      rw [hrst]; simp [θ,sub_smul,u]
    rw [he]; exact good_sum θ _ hθ hgood
  have hyj (j) : (w-u) j.succ = (y j : ℝ) := by
    simp [w,u,y, Nat.cast_sub (hrle j), hrr]
  have hfirst : (w-u) 0 = 1 := by simp [w,u,hk0]
  refine ⟨y,r,hzy,fun i => ?_,fun i => ?_,?_,?_⟩
  · have h := hrest.2 i; simp only [hyj,hfirst,mul_one] at h; exact_mod_cast h
  · have h := (hgood k).2 i; simp only [hk0,Int.cast_zero,mul_zero,← hrr] at h; exact_mod_cast h
  · by_contra! he
    have hzero (j) : r j = 0 := by
      have h := Finset.single_le_sum (f := r) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    apply hne k
    funext j
    exact Fin.cases hk0 (fun l => by simpa [hzero] using (hr l).symm) j
  · calc
      _ ≤ ∑ _ : Fin p, D := Finset.sum_le_sum fun j _ => by
        exact_mod_cast (hr j).le.trans ((le_abs_self _).trans (hbound k j.succ))
      _ = p*D := by simp
      _ ≤ p*(p+1)*D := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
      _ = _ := by dsimp [D]; ring
