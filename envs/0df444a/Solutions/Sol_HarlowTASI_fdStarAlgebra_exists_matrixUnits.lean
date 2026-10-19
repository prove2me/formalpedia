-- Prove2me | solution 1 for HarlowTASI.fdStarAlgebra_exists_matrixUnits
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T02:56:43.486812+00:00
-- url     : https://prove2.me/submissions/7ac0e3a7-6cc0-473f-beea-a09df175ac93

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

open Matrix Polynomial
open scoped ComplexOrder



namespace FDAux

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem aeval_spec (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (g : ℂ[X]) :
    aeval H g = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
      (diagonal (fun i => eval ((hH.eigenvalues i : ℝ) : ℂ) g)) := by
  conv_lhs => rw [hH.spectral_theorem]
  rw [aeval_algHom_apply]
  congr 1
  have : diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
      diagonalAlgHom ℂ (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := rfl
  rw [this, aeval_algHom_apply, aeval_pi_apply]
  rfl

theorem spec_proj (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (hne : H ≠ 0) :
    ∃ (f : ℂ[X]) (μ : ℂ), μ ≠ 0 ∧
      aeval H (X * f) * aeval H (X * f) = aeval H (X * f) ∧
      (aeval H (X * f))ᴴ = aeval H (X * f) ∧ aeval H (X * f) ≠ 0 ∧
      H * aeval H (X * f) = μ • aeval H (X * f) := by
  set U := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hH.eigenvectorUnitary
  set d : ι → ℂ := fun i => ((hH.eigenvalues i : ℝ) : ℂ)
  have hHd : H = U (diagonal d) := hH.spectral_theorem
  obtain ⟨i0, hi0⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    rw [hHd]
    have : d = 0 := funext h
    rw [this]; simp
  set μ := d i0
  set T := (Finset.univ.image d).erase μ
  set k : ℂ := μ * ∏ ν ∈ T, (μ - ν)
  have hk : k ≠ 0 := by
    refine mul_ne_zero hi0 (Finset.prod_ne_zero_iff.mpr fun ν hν => sub_ne_zero.mpr ?_)
    exact fun h => (Finset.ne_of_mem_erase hν) h.symm
  set f : ℂ[X] := C k⁻¹ * ∏ ν ∈ T, (X - C ν)
  set e : ι → ℂ := fun i => if d i = μ then 1 else 0
  have hev : ∀ i, eval (d i) (X * f) = e i := by
    intro i
    simp only [f, e, eval_mul, eval_X, eval_C, eval_prod, eval_sub, k]
    split_ifs with h
    · rw [h]
      have hp : ∏ ν ∈ T, (μ - ν) ≠ 0 := right_ne_zero_of_mul hk
      field_simp
    · have : ∏ ν ∈ T, (d i - ν) = 0 :=
        Finset.prod_eq_zero (i := d i) (Finset.mem_erase.mpr ⟨h, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
          (sub_self _)
      rw [this]; ring
  have hP : aeval H (X * f) = U (diagonal e) := by
    rw [aeval_spec H hH]
    congr 2
    funext i
    exact hev i
  refine ⟨f, μ, hi0, ?_, ?_, ?_, ?_⟩
  · rw [hP, ← map_mul, diagonal_mul_diagonal]
    congr 2; funext i; simp only [e]; split_ifs <;> simp
  · rw [hP, ← star_eq_conjTranspose, ← map_star, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 2; funext i; simp only [e, Pi.star_apply]; split_ifs <;> simp
  · rw [hP]
    intro h
    have h2 : diagonal e = 0 := by
      have := congrArg U.symm h
      simpa using this
    have := congrFun (congrFun h2 i0) i0
    simp [e, μ] at this
  · rw [hP, hHd, ← map_mul, diagonal_mul_diagonal, ← map_smul, ← diagonal_smul]
    congr 2; funext i; simp only [e]; split_ifs with h <;> simp [h]

/-- strict rank decrease -/
theorem rank_lt (q P : Matrix ι ι ℂ) (hq : q * q = q) (hP : P * P = P) (hPq : P * q = P)
    (hqP : q * P = P) (hne : P ≠ 0) :
    Module.finrank ℂ (LinearMap.range (mulVecLin (q - P))) <
      Module.finrank ℂ (LinearMap.range (mulVecLin q)) := by
  apply Submodule.finrank_lt_finrank_of_lt
  rw [lt_iff_le_and_ne]
  constructor
  · rintro _ ⟨w, rfl⟩
    refine ⟨(q - P) *ᵥ w, ?_⟩
    simp only [mulVecLin_apply, mulVec_mulVec, mul_sub, hq, hqP]
  · intro h
    obtain ⟨u, hu⟩ : ∃ u, P *ᵥ u ≠ 0 := by
      by_contra hc; push Not at hc
      apply hne
      exact Matrix.toLin'.injective (LinearMap.ext fun u => by simpa using hc u)
    have hmem : P *ᵥ u ∈ LinearMap.range (mulVecLin q) :=
      ⟨P *ᵥ u, by simp [mulVec_mulVec, hqP]⟩
    rw [← h] at hmem
    obtain ⟨w, hw⟩ := hmem
    simp only [mulVecLin_apply] at hw
    have := congrArg (fun z => P *ᵥ z) hw
    simp only [mulVec_mulVec, mul_sub, hPq, hP, sub_self, zero_mulVec] at this
    exact hu this.symm

end FDAux



namespace FDAux

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem aeval_mem' (M : StarSubalgebra ℂ (Matrix ι ι ℂ)) {H : Matrix ι ι ℂ} (hH : H ∈ M)
    (g : ℂ[X]) : aeval H g ∈ M := by
  have h1 : Algebra.adjoin ℂ {H} ≤ M.toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hH)
  exact h1 (aeval_mem_adjoin_singleton ℂ H)

theorem herm_scalar (M : StarSubalgebra ℂ (Matrix ι ι ℂ)) (q : Matrix ι ι ℂ)
    (hmin : ∀ P ∈ M, P * P = P → Pᴴ = P → q * P = P → P = 0 ∨ P = q)
    (H : Matrix ι ι ℂ) (hHM : H ∈ M) (hH : Hᴴ = H) (hqH : q * H = H) (hHq : H * q = H) :
    ∃ c : ℂ, H = c • q := by
  by_cases h0 : H = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨f, μ, -, h1, h2, h3, h4⟩ := spec_proj H hH h0
  have hPM : aeval H (X * f) ∈ M := aeval_mem' M hHM _
  have hqP : q * aeval H (X * f) = aeval H (X * f) := by
    rw [map_mul, aeval_X, ← Matrix.mul_assoc, hqH]
  rcases hmin _ hPM h1 h2 hqP with h | h
  · exact absurd h h3
  · refine ⟨μ, ?_⟩
    rw [← hHq, ← h, h4]

theorem min_proj (M : StarSubalgebra ℂ (Matrix ι ι ℂ)) (R : Matrix ι ι ℂ) (hRM : R ∈ M)
    (hR : R * R = R) (hRH : Rᴴ = R) (hne : R ≠ 0) :
    ∃ q ∈ M, q * q = q ∧ qᴴ = q ∧ q ≠ 0 ∧ R * q = q ∧
      ∀ X ∈ M, ∃ c : ℂ, q * X * q = c • q := by
  classical
  let p : ℕ → Prop := fun n => ∃ q ∈ M, q * q = q ∧ qᴴ = q ∧ q ≠ 0 ∧ R * q = q ∧
    Module.finrank ℂ (LinearMap.range (mulVecLin q)) = n
  have hex : ∃ n, p n := ⟨_, R, hRM, hR, hRH, hne, hR, rfl⟩
  obtain ⟨q, hqM, hq, hqH, hq0, hRq, hn⟩ := Nat.find_spec hex
  refine ⟨q, hqM, hq, hqH, hq0, hRq, ?_⟩
  have hmin : ∀ P ∈ M, P * P = P → Pᴴ = P → q * P = P → P = 0 ∨ P = q := by
    intro P hPM hP hPH hqP
    by_contra hc
    push Not at hc
    have hPq : P * q = P := by
      have := congrArg conjTranspose hqP
      rwa [conjTranspose_mul, hPH, hqH] at this
    have hlt := rank_lt q P hq hP hPq hqP hc.1
    have hp : p (Module.finrank ℂ (LinearMap.range (mulVecLin (q - P)))) := by
      refine ⟨q - P, sub_mem hqM hPM, ?_, ?_, sub_ne_zero.mpr hc.2.symm, ?_, rfl⟩
      · simp only [mul_sub, sub_mul, hq, hP, hPq, hqP]; abel
      · rw [conjTranspose_sub, hqH, hPH]
      · rw [mul_sub, hRq, ← hqP, ← Matrix.mul_assoc, hRq]
    have := Nat.find_min' hex hp
    omega
  intro X hX
  set Y := q * X * q
  have hYM : Y ∈ M := mul_mem (mul_mem hqM hX) hqM
  have hYHM : Yᴴ ∈ M := by rw [← star_eq_conjTranspose]; exact star_mem hYM
  have hqY : q * Y = Y := by simp only [Y, ← Matrix.mul_assoc, hq]
  have hYq : Y * q = Y := by simp only [Y, Matrix.mul_assoc, hq]
  have hqYH : q * Yᴴ = Yᴴ := by
    rw [← hYq, conjTranspose_mul, hqH, ← Matrix.mul_assoc, hq]
  have hYHq : Yᴴ * q = Yᴴ := by
    rw [← hqY, conjTranspose_mul, hqH, Matrix.mul_assoc, hq]
  obtain ⟨c1, hc1⟩ := herm_scalar M q hmin ((1/2 : ℂ) • (Y + Yᴴ))
    (M.smul_mem (add_mem hYM hYHM) _)
    (by rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]; simp)
    (by rw [mul_smul_comm, mul_add, hqY, hqYH]) (by rw [smul_mul_assoc, add_mul, hYq, hYHq])
  obtain ⟨c2, hc2⟩ := herm_scalar M q hmin ((-Complex.I/2 : ℂ) • (Y - Yᴴ))
    (M.smul_mem (sub_mem hYM hYHM) _)
    (by
      rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      have : star (-Complex.I / 2) = -(-Complex.I / 2) := by
        simp [Complex.ext_iff]; norm_num
      rw [this, neg_smul, ← smul_neg, neg_sub])
    (by rw [mul_smul_comm, mul_sub, hqY, hqYH]) (by rw [smul_mul_assoc, sub_mul, hYq, hYHq])
  refine ⟨c1 + Complex.I * c2, ?_⟩
  have : Y = (1/2 : ℂ) • (Y + Yᴴ) + Complex.I • ((-Complex.I/2 : ℂ) • (Y - Yᴴ)) := by
    rw [smul_smul]
    have : Complex.I * (-Complex.I / 2) = 1/2 := by
      rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; ring
    rw [this, ← smul_add]
    rw [add_add_sub_cancel, ← two_smul ℂ Y, smul_smul]; norm_num
  rw [this, hc1, hc2, smul_smul, add_smul]

end FDAux



namespace FDAux

structure St (ι : Type) where
  N : ℕ
  dr : ℕ → ℕ
  v : ℕ → ℕ → Matrix ι ι ℂ
  q : ℕ → Matrix ι ι ℂ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def St.S (s : St ι) : Matrix ι ι ℂ :=
  ∑ a ∈ Finset.range s.N, ∑ i ∈ Finset.range (s.dr a), s.v a i * (s.v a i)ᴴ

structure St.Valid (M : StarSubalgebra ℂ (Matrix ι ι ℂ)) (s : St ι) : Prop where
  dpos : ∀ a < s.N, 0 < s.dr a
  vmem : ∀ a < s.N, ∀ i < s.dr a, s.v a i ∈ M
  orth : ∀ a < s.N, ∀ i < s.dr a, ∀ b < s.N, ∀ j < s.dr b,
    (s.v a i)ᴴ * s.v b j = if a = b ∧ i = j then s.q a else 0
  vq : ∀ a < s.N, ∀ i < s.dr a, s.v a i * s.q a = s.v a i
  qmem : ∀ a < s.N, s.q a ∈ M
  qidem : ∀ a < s.N, s.q a * s.q a = s.q a
  qherm : ∀ a < s.N, (s.q a)ᴴ = s.q a
  qne : ∀ a < s.N, s.q a ≠ 0
  qmin : ∀ a < s.N, ∀ X ∈ M, ∃ c : ℂ, s.q a * X * s.q a = c • s.q a
  qsep : ∀ a < s.N, ∀ b < s.N, a ≠ b → ∀ X ∈ M, s.q a * X * s.q b = 0

variable {M : StarSubalgebra ℂ (Matrix ι ι ℂ)}

theorem cT_mem {X : Matrix ι ι ℂ} (h : X ∈ M) : Xᴴ ∈ M := by
  rw [← star_eq_conjTranspose]; exact star_mem h

theorem St.S_mem {s : St ι} (hs : s.Valid M) : s.S ∈ M := by
  refine sum_mem fun a ha => sum_mem fun i hi => ?_
  rw [Finset.mem_range] at ha hi
  exact mul_mem (hs.vmem a ha i hi) (cT_mem (hs.vmem a ha i hi))

theorem St.S_herm (s : St ι) : (s.S)ᴴ = s.S := by
  simp only [St.S, conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose]

theorem St.S_v {s : St ι} (hs : s.Valid M) {a : ℕ} (ha : a < s.N) {i : ℕ} (hi : i < s.dr a) :
    s.S * s.v a i = s.v a i := by
  simp only [St.S, Finset.sum_mul, Matrix.mul_assoc]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single i]
  · rw [hs.orth a ha i hi a ha i hi, if_pos ⟨rfl, rfl⟩, hs.vq a ha i hi]
  · intro j hj hji
    rw [Finset.mem_range] at hj
    rw [hs.orth a ha j hj a ha i hi, if_neg (by omega), Matrix.mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr hi) h
  · intro b hb hba
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hb hj
    rw [hs.orth b hb j hj a ha i hi, if_neg (by omega), Matrix.mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr ha) h

theorem St.S_idem {s : St ι} (hs : s.Valid M) : s.S * s.S = s.S := by
  nth_rewrite 2 [St.S]
  simp only [Finset.mul_sum]
  conv_rhs => rw [St.S]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at ha hi
  rw [← Matrix.mul_assoc, St.S_v hs ha hi]

theorem St.R_v {s : St ι} (hs : s.Valid M) {a : ℕ} (ha : a < s.N) {i : ℕ} (hi : i < s.dr a) :
    (1 - s.S) * s.v a i = 0 := by
  rw [sub_mul, St.S_v hs ha hi, Matrix.one_mul, sub_self]

theorem St.R_idem {s : St ι} (hs : s.Valid M) : (1 - s.S) * (1 - s.S) = 1 - s.S := by
  simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, St.S_idem hs]; abel

theorem St.R_herm (s : St ι) : (1 - s.S)ᴴ = 1 - s.S := by
  rw [conjTranspose_sub, conjTranspose_one, St.S_herm]

/-- vectors in the range of R are orthogonal to the v's -/
theorem St.orth_R {s : St ι} (hs : s.Valid M) {w : Matrix ι ι ℂ} (hw : (1 - s.S) * w = w)
    {a : ℕ} (ha : a < s.N) {i : ℕ} (hi : i < s.dr a) :
    wᴴ * s.v a i = 0 ∧ (s.v a i)ᴴ * w = 0 := by
  have h1 : wᴴ * s.v a i = 0 := by
    rw [← hw, conjTranspose_mul, St.R_herm, Matrix.mul_assoc, St.R_v hs ha hi, Matrix.mul_zero]
  refine ⟨h1, ?_⟩
  have := congrArg conjTranspose h1
  rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this

def St.addOld (s : St ι) (a : ℕ) (w : Matrix ι ι ℂ) : St ι where
  N := s.N
  dr := Function.update s.dr a (s.dr a + 1)
  v := fun b i => if b = a ∧ i = s.dr a then w else s.v b i
  q := s.q

theorem St.addOld_old {s : St ι} {a b i : ℕ} (hi : i < Function.update s.dr a (s.dr a + 1) b)
    (h : ¬ (b = a ∧ i = s.dr a)) : i < s.dr b := by
  rw [Function.update_apply] at hi
  split_ifs at hi with hb
  · subst hb; omega
  · exact hi

theorem St.addOld_valid {s : St ι} (hs : s.Valid M) {a : ℕ} (ha : a < s.N) {w : Matrix ι ι ℂ}
    (hwM : w ∈ M) (hww : wᴴ * w = s.q a) (hwq : w * s.q a = w) (hR : (1 - s.S) * w = w) :
    (s.addOld a w).Valid M ∧ (s.addOld a w).S = s.S + w * wᴴ := by
  have hdr : ∀ b, (s.addOld a w).dr b = Function.update s.dr a (s.dr a + 1) b := fun _ => rfl
  constructor
  · constructor
    · intro b hb
      change 0 < Function.update s.dr a (s.dr a + 1) b
      rw [Function.update_apply]; split_ifs
      · omega
      · exact hs.dpos b hb
    · intro b hb i hi
      change (if b = a ∧ i = s.dr a then w else s.v b i) ∈ M
      split_ifs with h
      · exact hwM
      · exact hs.vmem b hb i (St.addOld_old hi h)
    · intro b hb i hi c hc j hj
      change (if b = a ∧ i = s.dr a then w else s.v b i)ᴴ *
        (if c = a ∧ j = s.dr a then w else s.v c j) = if b = c ∧ i = j then s.q b else 0
      by_cases h1 : b = a ∧ i = s.dr a <;> by_cases h2 : c = a ∧ j = s.dr a
      · rw [if_pos h1, if_pos h2, if_pos ⟨by omega, by omega⟩, hww, h1.1]
      · have hj' := St.addOld_old hj h2
        rw [if_pos h1, if_neg h2, (St.orth_R hs hR hc hj').1, if_neg]
        rintro ⟨rfl, rfl⟩; exact h2 ⟨h1.1, h1.2⟩
      · have hi' := St.addOld_old hi h1
        rw [if_neg h1, if_pos h2, (St.orth_R hs hR hb hi').2, if_neg]
        rintro ⟨rfl, rfl⟩; exact h1 ⟨h2.1, h2.2⟩
      · rw [if_neg h1, if_neg h2]
        exact hs.orth b hb i (St.addOld_old hi h1) c hc j (St.addOld_old hj h2)
    · intro b hb i hi
      change (if b = a ∧ i = s.dr a then w else s.v b i) * s.q b =
        (if b = a ∧ i = s.dr a then w else s.v b i)
      split_ifs with h
      · rw [h.1]; exact hwq
      · exact hs.vq b hb i (St.addOld_old hi h)
    · exact hs.qmem
    · exact hs.qidem
    · exact hs.qherm
    · exact hs.qne
    · exact hs.qmin
    · exact hs.qsep
  · simp only [St.S]
    change ∑ b ∈ Finset.range s.N, ∑ i ∈ Finset.range (Function.update s.dr a (s.dr a + 1) b),
      (if b = a ∧ i = s.dr a then w else s.v b i) *
        (if b = a ∧ i = s.dr a then w else s.v b i)ᴴ = _
    have : ∀ b ∈ Finset.range s.N,
        ∑ i ∈ Finset.range (Function.update s.dr a (s.dr a + 1) b),
          (if b = a ∧ i = s.dr a then w else s.v b i) *
            (if b = a ∧ i = s.dr a then w else s.v b i)ᴴ =
        ∑ i ∈ Finset.range (s.dr b), s.v b i * (s.v b i)ᴴ + if b = a then w * wᴴ else 0 := by
      intro b _
      by_cases hb : b = a
      · subst hb
        rw [Function.update_self, Finset.sum_range_succ, if_pos ⟨rfl, rfl⟩, if_pos rfl]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [if_neg (by omega)]
      · rw [Function.update_of_ne hb, if_neg hb, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [if_neg (by tauto)]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_range.mpr ha)]

def St.addNew (s : St ι) (w : Matrix ι ι ℂ) : St ι where
  N := s.N + 1
  dr := Function.update s.dr s.N 1
  v := fun b i => if b = s.N then w else s.v b i
  q := Function.update s.q s.N w

theorem St.addNew_valid {s : St ι} (hs : s.Valid M) {w : Matrix ι ι ℂ}
    (hwM : w ∈ M) (hw2 : w * w = w) (hwH : wᴴ = w) (hw0 : w ≠ 0)
    (hwmin : ∀ X ∈ M, ∃ c : ℂ, w * X * w = c • w)
    (hsep : ∀ a < s.N, ∀ X ∈ M, w * X * s.q a = 0) (hR : (1 - s.S) * w = w) :
    (s.addNew w).Valid M ∧ (s.addNew w).S = s.S + w * wᴴ := by
  have hN : (s.addNew w).N = s.N + 1 := rfl
  have hdr : ∀ b, b ≠ s.N → (s.addNew w).dr b = s.dr b := fun b hb => Function.update_of_ne hb _ _
  have hdrN : (s.addNew w).dr s.N = 1 := Function.update_self _ _ _
  have hv : ∀ b i, b ≠ s.N → (s.addNew w).v b i = s.v b i := fun b i hb => if_neg hb
  have hvN : ∀ i, (s.addNew w).v s.N i = w := fun i => if_pos rfl
  have hq : ∀ b, b ≠ s.N → (s.addNew w).q b = s.q b := fun b hb => Function.update_of_ne hb _ _
  have hqN : (s.addNew w).q s.N = w := Function.update_self _ _ _
  constructor
  · constructor
    · intro b hb
      by_cases h : b = s.N
      · subst h; rw [hdrN]; omega
      · rw [hdr b h]; exact hs.dpos b (by rw [hN] at hb; omega)
    · intro b hb i hi
      by_cases h : b = s.N
      · subst h; rw [hvN]; exact hwM
      · rw [hdr b h] at hi; rw [hv b i h]; exact hs.vmem b (by rw [hN] at hb; omega) i hi
    · intro b hb i hi c hc j hj
      rw [hN] at hb hc
      by_cases h1 : b = s.N <;> by_cases h2 : c = s.N
      · subst h1 h2; rw [hdrN] at hi hj
        rw [hvN, hvN, if_pos ⟨rfl, by omega⟩, hqN, hwH, hw2]
      · rw [hdr c h2] at hj; subst h1
        rw [hvN, hv c j h2, (St.orth_R hs hR (by omega) hj).1, if_neg (by omega)]
      · rw [hdr b h1] at hi; subst h2
        rw [hvN, hv b i h1, (St.orth_R hs hR (by omega) hi).2, if_neg (by omega)]
      · rw [hdr b h1] at hi; rw [hdr c h2] at hj
        rw [hv b i h1, hv c j h2, hq b h1]
        exact hs.orth b (by omega) i hi c (by omega) j hj
    · intro b hb i hi
      rw [hN] at hb
      by_cases h : b = s.N
      · subst h; rw [hvN, hqN, hw2]
      · rw [hdr b h] at hi; rw [hv b i h, hq b h]; exact hs.vq b (by omega) i hi
    · intro b hb; rw [hN] at hb
      by_cases h : b = s.N
      · subst h; rw [hqN]; exact hwM
      · rw [hq b h]; exact hs.qmem b (by omega)
    · intro b hb; rw [hN] at hb
      by_cases h : b = s.N
      · subst h; rw [hqN]; exact hw2
      · rw [hq b h]; exact hs.qidem b (by omega)
    · intro b hb; rw [hN] at hb
      by_cases h : b = s.N
      · subst h; rw [hqN]; exact hwH
      · rw [hq b h]; exact hs.qherm b (by omega)
    · intro b hb; rw [hN] at hb
      by_cases h : b = s.N
      · subst h; rw [hqN]; exact hw0
      · rw [hq b h]; exact hs.qne b (by omega)
    · intro b hb; rw [hN] at hb
      by_cases h : b = s.N
      · subst h; rw [hqN]; exact hwmin
      · rw [hq b h]; exact hs.qmin b (by omega)
    · intro b hb c hc hbc X hX
      rw [hN] at hb hc
      by_cases h1 : b = s.N <;> by_cases h2 : c = s.N
      · exact absurd (h1.trans h2.symm) hbc
      · subst h1; rw [hqN, hq c h2]; exact hsep c (by omega) X hX
      · subst h2; rw [hqN, hq b h1]
        have := congrArg conjTranspose (hsep b (by omega) Xᴴ (cT_mem hX))
        simpa only [conjTranspose_mul, conjTranspose_conjTranspose, hwH, hs.qherm b (by omega),
          conjTranspose_zero, Matrix.mul_assoc] using this
      · rw [hq b h1, hq c h2]; exact hs.qsep b (by omega) c (by omega) hbc X hX
  · simp only [St.S]
    rw [hN, Finset.sum_range_succ, hdrN, Finset.sum_range_one, hvN]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_range] at hb
    rw [hdr b (by omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hv b i (by omega)]

theorem trace_cTm (A : Matrix ι ι ℂ) :
    trace (Aᴴ * A) = ((∑ i, ∑ j, ‖A j i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [trace, diag, mul_apply, conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

theorem trace_pos (A : Matrix ι ι ℂ) (h : A ≠ 0) : 0 < ∑ i, ∑ j, ‖A j i‖ ^ 2 := by
  obtain ⟨j, i, hji⟩ : ∃ j i, A j i ≠ 0 := by
    by_contra hc; push Not at hc; exact h (Matrix.ext hc)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖A j i‖ ^ 2)
    (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ i))
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => ‖A j i‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ j))
  exact pow_pos (norm_pos_iff.mpr hji) 2

theorem pos_scalar (y q : Matrix ι ι ℂ) (hy : y ≠ 0) (hq : q ≠ 0) (hqq : q * q = q)
    (hqH : qᴴ = q) (c : ℂ) (hc : yᴴ * y = c • q) : ∃ r : ℝ, 0 < r ∧ c = r := by
  have h1 := congrArg trace hc
  rw [trace_smul, ← hqq, ← congrArg (· * q) hqH, trace_cTm, trace_cTm, smul_eq_mul] at h1
  have hp1 := trace_pos y hy
  have hp2 := trace_pos q hq
  refine ⟨(∑ i, ∑ j, ‖y j i‖ ^ 2) / (∑ i, ∑ j, ‖q j i‖ ^ 2), div_pos hp1 hp2, ?_⟩
  rw [Complex.ofReal_div, h1, mul_div_assoc, div_self (by exact_mod_cast hp2.ne'), mul_one]

end FDAux



namespace FDAux

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : StarSubalgebra ℂ (Matrix ι ι ℂ)}

theorem St.qv {s : St ι} (hs : s.Valid M) {a : ℕ} (ha : a < s.N) {i : ℕ} (hi : i < s.dr a) :
    s.q a * (s.v a i)ᴴ = (s.v a i)ᴴ := by
  have := congrArg conjTranspose (hs.vq a ha i hi)
  rwa [conjTranspose_mul, hs.qherm a ha] at this

theorem St.step {s : St ι} (hs : s.Valid M) (hR0 : 1 - s.S ≠ 0) :
    ∃ s' : St ι, s'.Valid M ∧
      Module.finrank ℂ (LinearMap.range (mulVecLin (1 - s'.S))) <
        Module.finrank ℂ (LinearMap.range (mulVecLin (1 - s.S))) := by
  obtain ⟨q', hq'M, hq'2, hq'H, hq'0, hRq', hq'min⟩ :=
    min_proj M (1 - s.S) (sub_mem (one_mem _) (St.S_mem hs)) (St.R_idem hs) (St.R_herm s) hR0
  have key : ∀ (s' : St ι) (w : Matrix ι ι ℂ), s'.S = s.S + w * wᴴ → (1 - s.S) * w = w →
      (w * wᴴ) * (w * wᴴ) = w * wᴴ → w ≠ 0 →
      Module.finrank ℂ (LinearMap.range (mulVecLin (1 - s'.S))) <
        Module.finrank ℂ (LinearMap.range (mulVecLin (1 - s.S))) := by
    intro s' w hS hRw hP hw0
    have : 1 - s'.S = (1 - s.S) - w * wᴴ := by rw [hS]; abel
    rw [this]
    apply rank_lt _ _ (St.R_idem hs) hP
    · rw [Matrix.mul_assoc]; congr 1
      have := congrArg conjTranspose hRw
      rwa [conjTranspose_mul, St.R_herm] at this
    · rw [← Matrix.mul_assoc, hRw]
    · exact fun h => hw0 (self_mul_conjTranspose_eq_zero.mp h)
  by_cases hex : ∃ a < s.N, ∃ X ∈ M, q' * X * s.q a ≠ 0
  · obtain ⟨a, ha, X, hX, hy⟩ := hex
    set y := q' * X * s.q a with hy_def
    obtain ⟨c, hc⟩ := hs.qmin a ha (Xᴴ * q' * X) (mul_mem (mul_mem (cT_mem hX) hq'M) hX)
    have hyy : yᴴ * y = c • s.q a := by
      rw [← hc, hy_def]
      simp only [conjTranspose_mul, hq'H, hs.qherm a ha, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc q' q', hq'2]
    obtain ⟨r, hr, rfl⟩ := pos_scalar y (s.q a) hy (hs.qne a ha) (hs.qidem a ha) (hs.qherm a ha) c hyy
    set t : ℝ := (Real.sqrt r)⁻¹
    have ht : t * t * r = 1 := by
      have := Real.mul_self_sqrt hr.le
      have h0 : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
      simp only [t]; field_simp; linarith
    set w := (t : ℂ) • y
    have hyM : y ∈ M := mul_mem (mul_mem hq'M hX) (hs.qmem a ha)
    have hwM : w ∈ M := M.smul_mem hyM _
    have hww : wᴴ * w = s.q a := by
      simp only [w, conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hyy]
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← mul_assoc, ht,
        Complex.ofReal_one, one_smul]
    have hwq : w * s.q a = w := by
      simp only [w, smul_mul_assoc, hy_def, Matrix.mul_assoc, hs.qidem a ha]
    have hRw : (1 - s.S) * w = w := by
      simp only [w, mul_smul_comm, hy_def, ← Matrix.mul_assoc, hRq']
    obtain ⟨hv, hS⟩ := St.addOld_valid hs ha hwM hww hwq hRw
    refine ⟨_, hv, key _ w hS hRw ?_ ?_⟩
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc wᴴ, hww, ← Matrix.mul_assoc, hwq]
    · intro h; apply hs.qne a ha; rw [← hww, h, conjTranspose_zero, Matrix.zero_mul]
  · push Not at hex
    obtain ⟨hv, hS⟩ := St.addNew_valid hs hq'M hq'2 hq'H hq'0 hq'min hex hRq'
    refine ⟨_, hv, key _ q' hS hRq' ?_ hq'0⟩
    rw [hq'H, hq'2, hq'2]

theorem St.exists_final : ∃ s : St ι, s.Valid M ∧ s.S = 1 := by
  have : ∀ n, ∀ s : St ι, s.Valid M →
      Module.finrank ℂ (LinearMap.range (mulVecLin (1 - s.S))) = n →
      ∃ s' : St ι, s'.Valid M ∧ s'.S = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs hn
      by_cases h : 1 - s.S = 0
      · exact ⟨s, hs, (sub_eq_zero.mp h).symm⟩
      · obtain ⟨s', hs', hlt⟩ := St.step hs h
        exact ih _ (hn ▸ hlt) s' hs' rfl
  let s0 : St ι := ⟨0, fun _ => 0, fun _ _ => 0, fun _ => 0⟩
  have hs0 : s0.Valid M := by
    constructor <;> intro a ha <;> exact absurd ha (Nat.not_lt_zero _)
  exact this _ s0 hs0 rfl

end FDAux

theorem solution {C : Type} [Fintype C] [DecidableEq C]
    (M : StarSubalgebra ℂ (Matrix C C ℂ)) :
    ∃ (N : ℕ) (dr : Fin N → ℕ) (e : (a : Fin N) → Fin (dr a) → Fin (dr a) → Matrix C C ℂ),
      (∀ a, 0 < dr a) ∧
      (∀ a i j k l, e a i j * e a k l = if j = k then e a i l else 0) ∧
      (∀ a b i j k l, a ≠ b → e a i j * e b k l = 0) ∧
      (∀ a i j, (e a i j)ᴴ = e a j i) ∧
      (∀ a i, e a i i ≠ 0) ∧
      ∑ a, ∑ i, e a i i = 1 ∧
      (M : Set (Matrix C C ℂ)) =
        {X | ∃ x : ∀ a, Matrix (Fin (dr a)) (Fin (dr a)) ℂ,
          X = ∑ a, ∑ i, ∑ j, x a i j • e a i j} := by
  obtain ⟨s, hs, hS⟩ := FDAux.St.exists_final (M := M)
  have hS' : ∑ a : Fin s.N, ∑ i : Fin (s.dr a), s.v a i * (s.v a i)ᴴ = 1 := by
    rw [← hS, FDAux.St.S, Finset.sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_range]
  refine ⟨s.N, fun a => s.dr a.1, fun a i j => s.v a.1 i.1 * (s.v a.1 j.1)ᴴ,
    fun a => hs.dpos a.1 a.2, ?_, ?_, ?_, ?_, hS', ?_⟩
  · intro a i j k l
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (s.v a j)ᴴ, hs.orth a a.2 j j.2 a a.2 k k.2]
    by_cases hjk : j = k
    · rw [if_pos hjk, if_pos ⟨rfl, congrArg Fin.val hjk⟩, ← Matrix.mul_assoc, hs.vq a a.2 i i.2]
    · rw [if_neg hjk, if_neg (fun h => hjk (Fin.ext h.2)), Matrix.zero_mul, Matrix.mul_zero]
  · intro a b i j k l hab
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (s.v a j)ᴴ, hs.orth a a.2 j j.2 b b.2 k k.2,
      if_neg (fun h => hab (Fin.ext h.1)), Matrix.zero_mul, Matrix.mul_zero]
  · intro a i j
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  · intro a i h
    have h0 := self_mul_conjTranspose_eq_zero.mp h
    have := hs.orth a a.2 i i.2 a a.2 i i.2
    rw [if_pos ⟨rfl, rfl⟩, h0, conjTranspose_zero, Matrix.zero_mul] at this
    exact hs.qne a a.2 this.symm
  · ext X
    constructor
    · intro hX
      have hx : ∀ (a : Fin s.N) (i j : Fin (s.dr a)),
          ∃ c : ℂ, (s.v a i)ᴴ * X * s.v a j = c • s.q a := by
        intro a i j
        obtain ⟨c, hc⟩ := hs.qmin a a.2 ((s.v a i)ᴴ * X * s.v a j)
          (mul_mem (mul_mem (FDAux.cT_mem (hs.vmem a a.2 i i.2)) hX) (hs.vmem a a.2 j j.2))
        refine ⟨c, ?_⟩
        rw [← hc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, FDAux.St.qv hs a.2 i.2,
          Matrix.mul_assoc _ _ (s.q a), hs.vq a a.2 j j.2]
      choose x hx using hx
      refine ⟨x, ?_⟩
      calc X = 1 * X * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
        _ = ∑ a : Fin s.N, ∑ i : Fin (s.dr a), ∑ b : Fin s.N, ∑ j : Fin (s.dr b),
              s.v a i * ((s.v a i)ᴴ * X * s.v b j) * (s.v b j)ᴴ := by
          rw [← hS', Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Matrix.mul_assoc]
        _ = _ := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single a]
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [hx a i j, Matrix.mul_smul, Matrix.smul_mul, hs.vq a a.2 i i.2]
          · intro b _ hba
            refine Finset.sum_eq_zero fun j _ => ?_
            have : (s.v a i)ᴴ * X * s.v b j = 0 := by
              rw [← FDAux.St.qv hs a.2 i.2, ← hs.vq b b.2 j j.2]
              have := hs.qsep a a.2 b b.2 (fun h => hba (Fin.ext h).symm)
                ((s.v a i)ᴴ * X * s.v b j)
                (mul_mem (mul_mem (FDAux.cT_mem (hs.vmem a a.2 i i.2)) hX) (hs.vmem b b.2 j j.2))
              simpa only [Matrix.mul_assoc] using this
            rw [this, Matrix.mul_zero, Matrix.zero_mul]
          · intro h; exact absurd (Finset.mem_univ a) h
    · rintro ⟨x, rfl⟩
      exact sum_mem fun a _ => sum_mem fun i _ => sum_mem fun j _ => M.smul_mem
        (mul_mem (hs.vmem a a.2 i i.2) (FDAux.cT_mem (hs.vmem a a.2 j j.2))) _

