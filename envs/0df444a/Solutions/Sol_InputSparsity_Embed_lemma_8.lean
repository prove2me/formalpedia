-- Prove2me | solution 1 for InputSparsity.Embed.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:00:45.075984+00:00
-- url     : https://prove2.me/submissions/00c2b7f4-d492-40b8-951f-5f26f548e2fb

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

open Matrix

noncomputable section

namespace Aux_InputSparsity_Embed_lemma_8

open InputSparsity.Embed

/-! ### Quadratic-form algebra -/

def Qv {m : ℕ} (v : Fin m → ℝ) : ℝ := v ⬝ᵥ v

def Gd {k r : ℕ} (M : Matrix (Fin k) (Fin r) ℝ) (c : Fin r → ℝ) : ℝ :=
  Qv (M *ᵥ c) - Qv c

def Bl {k r : ℕ} (M : Matrix (Fin k) (Fin r) ℝ) (u v : Fin r → ℝ) : ℝ :=
  (M *ᵥ u) ⬝ᵥ (M *ᵥ v) - u ⬝ᵥ v

theorem Qv_eq {m : ℕ} (v : Fin m → ℝ) : Qv v = ∑ i, v i ^ 2 := by
  unfold Qv dotProduct
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sqNorm_eq_Qv {m : ℕ} (v : Fin m → ℝ) : sqNorm v = Qv v := by
  rw [Qv_eq]; rfl

theorem Qv_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ Qv v := by
  rw [Qv_eq]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem Qv_smul {m : ℕ} (t : ℝ) (v : Fin m → ℝ) : Qv (t • v) = t ^ 2 * Qv v := by
  simp only [Qv, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem Gd_smul {k r : ℕ} (M : Matrix (Fin k) (Fin r) ℝ) (t : ℝ) (c : Fin r → ℝ) :
    Gd M (t • c) = t ^ 2 * Gd M c := by
  simp only [Gd, Matrix.mulVec_smul, Qv_smul]
  ring

theorem Bl_smul_left {k r : ℕ} (M : Matrix (Fin k) (Fin r) ℝ) (t : ℝ) (u v : Fin r → ℝ) :
    Bl M (t • u) v = t * Bl M u v := by
  simp only [Bl, Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem Gd_sub {k r : ℕ} (M : Matrix (Fin k) (Fin r) ℝ) (w d : Fin r → ℝ) :
    Gd M (w - d) = Gd M w - 2 * Bl M w d + Gd M d := by
  simp only [Gd, Qv, Bl, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [dotProduct_comm (M *ᵥ d) (M *ᵥ w), dotProduct_comm d w]
  ring

theorem polar {k r : ℕ} (M : Matrix (Fin k) (Fin r) ℝ) (u v : Fin r → ℝ) :
    4 * Bl M u v = Gd M (u + v) - Gd M (u - v) := by
  simp only [Gd, Qv, Bl, Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, add_dotProduct,
    dotProduct_sub, sub_dotProduct]
  rw [dotProduct_comm (M *ᵥ v) (M *ᵥ u), dotProduct_comm v u]
  ring

theorem parallelogram {r : ℕ} (u v : Fin r → ℝ) :
    Qv (u + v) + Qv (u - v) = 2 * Qv u + 2 * Qv v := by
  simp only [Qv, dotProduct_add, add_dotProduct, dotProduct_sub, sub_dotProduct]
  rw [dotProduct_comm v u]
  ring

def InS {k r : ℕ} (M : Matrix (Fin k) (Fin r) ℝ) (μ : ℝ) : Prop :=
  0 ≤ μ ∧ ∀ c, |Gd M c| ≤ μ * Qv c

theorem Bl_bound {k r : ℕ} {M : Matrix (Fin k) (Fin r) ℝ} {μ : ℝ} (hμ : InS M μ)
    (u v : Fin r → ℝ) : |Bl M u v| ≤ μ * (Qv u + Qv v) / 2 := by
  have h4 := polar M u v
  have h1 := abs_le.mp (hμ.2 (u + v))
  have h2 := abs_le.mp (hμ.2 (u - v))
  have hp : μ * Qv (u + v) + μ * Qv (u - v) = 2 * μ * Qv u + 2 * μ * Qv v := by
    rw [← mul_add, parallelogram]; ring
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem two_Bl_bound {k r : ℕ} {M : Matrix (Fin k) (Fin r) ℝ} {μ : ℝ} (hμ : InS M μ)
    (w d : Fin r → ℝ) : 2 * |Bl M w d| ≤ μ * (Qv w / 8 + 8 * Qv d) := by
  have h := Bl_bound hμ ((1 / 8 : ℝ) • w) d
  rw [Bl_smul_left, Qv_smul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8),
    show ((1 : ℝ) / 8) ^ 2 = 1 / 64 by norm_num] at h
  linarith

theorem exists_InS {k r : ℕ} (M : Matrix (Fin k) (Fin r) ℝ) : ∃ μ, InS M μ := by
  have hF : 0 ≤ ∑ i, ∑ a, M i a ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun a _ => sq_nonneg _))
  refine ⟨(∑ i, ∑ a, M i a ^ 2) + 1, by linarith, fun c => ?_⟩
  have hMc : Qv (M *ᵥ c) ≤ (∑ i, ∑ a, M i a ^ 2) * Qv c := by
    rw [Qv_eq, Qv_eq, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h1 := Qv_nonneg (M *ᵥ c)
  have h2 := Qv_nonneg c
  have h3 := mul_nonneg hF h2
  unfold Gd
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Rounding to the integer lattice -/

def flr {r : ℕ} (w : Fin r → ℝ) : Fin r → ℝ := fun a => ((⌊w a⌋ : ℤ) : ℝ)

theorem round_bounds {r : ℕ} (w : Fin r → ℝ) :
    Qv (w - flr w) ≤ r ∧ Qv (flr w) ≤ 2 * Qv w + 2 * r := by
  have hd : ∀ a, 0 ≤ w a - flr w a ∧ w a - flr w a < 1 := by
    intro a
    simp only [flr]
    constructor
    · linarith [Int.floor_le (w a)]
    · linarith [Int.lt_floor_add_one (w a)]
  have h1 : Qv (w - flr w) ≤ r := by
    rw [Qv_eq]
    calc ∑ a, (w - flr w) a ^ 2 ≤ ∑ _a : Fin r, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          rw [Pi.sub_apply]
          obtain ⟨h0, h1⟩ := hd a
          nlinarith
      _ = r := by simp
  refine ⟨h1, ?_⟩
  have h2 : Qv (flr w) ≤ 2 * Qv w + 2 * Qv (w - flr w) := by
    rw [Qv_eq, Qv_eq, Qv_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun a _ => ?_)
    rw [Pi.sub_apply]
    nlinarith [sq_nonneg (w a + (w a - flr w a))]
  linarith

def NetHyp {k r : ℕ} (M : Matrix (Fin k) (Fin r) ℝ) (ε : ℝ) : Prop :=
  ∀ z : Fin r → ℤ, ∑ a, (z a) ^ 2 ≤ 130 * (r : ℤ) →
    |Gd M (fun a => (z a : ℝ))| ≤ ε / 6 * Qv (fun a => (z a : ℝ))

theorem step {k r : ℕ} (M : Matrix (Fin k) (Fin r) ℝ) (ε μ : ℝ) (hε : 0 ≤ ε) (hμ : InS M μ)
    (hnet : NetHyp M ε) (w : Fin r → ℝ) (hw : Qv w = 64 * r) :
    |Gd M w| ≤ ε / 6 * (130 * r) + 17 * μ * r := by
  obtain ⟨hd, hz⟩ := round_bounds w
  have hzw : flr w = w - (w - flr w) := (sub_sub_cancel w (flr w)).symm
  have hG := Gd_sub M w (w - flr w)
  rw [← hzw] at hG
  have hQz : Qv (flr w) ≤ 130 * r := by linarith
  have hzint : ∑ a, (⌊w a⌋) ^ 2 ≤ 130 * (r : ℤ) := by
    have h1 := hQz
    rw [Qv_eq] at h1
    have h2 : ((∑ a, (⌊w a⌋) ^ 2 : ℤ) : ℝ) ≤ ((130 * (r : ℤ) : ℤ) : ℝ) := by
      push_cast
      simpa [flr] using h1
    exact Int.cast_le.mp h2
  have h1 : |Gd M (flr w)| ≤ ε / 6 * Qv (flr w) := hnet (fun a => ⌊w a⌋) hzint
  have h2 := two_Bl_bound hμ w (w - flr w)
  rw [hw] at h2
  have h3 := hμ.2 (w - flr w)
  have h4 : μ * Qv (w - flr w) ≤ μ * r := mul_le_mul_of_nonneg_left hd hμ.1
  have h5 : ε / 6 * Qv (flr w) ≤ ε / 6 * (130 * r) :=
    mul_le_mul_of_nonneg_left hQz (by linarith)
  have e1 := abs_le.mp h1
  have e3 := abs_le.mp h3
  have e2 := abs_le.mp (le_refl |Bl M w (w - flr w)|)
  rw [abs_le]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

theorem step_all {k r : ℕ} (M : Matrix (Fin k) (Fin r) ℝ) (ε μ : ℝ) (hε : 0 ≤ ε)
    (hμ : InS M μ) (hnet : NetHyp M ε) : InS M (130 * ε / 384 + 17 / 64 * μ) := by
  refine ⟨by linarith [hμ.1], fun c => ?_⟩
  rcases (Qv_nonneg c).eq_or_lt with h0 | hpos
  · have h := hμ.2 c
    rw [← h0, mul_zero] at h
    rw [← h0, mul_zero]
    exact h
  · have hr : (0 : ℝ) < r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h
        simp [Qv_eq] at hpos
      · exact_mod_cast h
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sqrt (64 * r / Qv c) := ⟨_, rfl⟩
    have ht2 : t ^ 2 = 64 * r / Qv c := by
      rw [ht]
      exact Real.sq_sqrt (div_pos (by linarith) hpos).le
    have hw : Qv (t • c) = 64 * r := by
      rw [Qv_smul, ht2, div_mul_cancel₀ _ hpos.ne']
    have h := step M ε μ hε hμ hnet (t • c) hw
    rw [Gd_smul, abs_mul, abs_of_nonneg (sq_nonneg t), ht2] at h
    have e : 64 * r / Qv c * |Gd M c| * Qv c = 64 * r * |Gd M c| := by
      rw [show 64 * r / Qv c * |Gd M c| * Qv c = |Gd M c| * (64 * r / Qv c * Qv c) by ring,
        div_mul_cancel₀ _ hpos.ne']
      ring
    have h' : 64 * r * |Gd M c| ≤ (ε / 6 * (130 * r) + 17 * μ * r) * Qv c := by
      rw [← e]
      exact mul_le_mul_of_nonneg_right h hpos.le
    refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < 64 * r by linarith)
    calc 64 * r * |Gd M c| ≤ (ε / 6 * (130 * r) + 17 * μ * r) * Qv c := h'
      _ = 64 * r * ((130 * ε / 384 + 17 / 64 * μ) * Qv c) := by ring

theorem final_bound {k r : ℕ} (M : Matrix (Fin k) (Fin r) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hnet : NetHyp M ε) : ∀ c, |Gd M c| ≤ ε * Qv c := by
  obtain ⟨μ0, hμ0⟩ := exists_InS M
  have hne : ({μ | InS M μ} : Set ℝ).Nonempty := ⟨μ0, hμ0⟩
  have hbdd : BddBelow ({μ | InS M μ} : Set ℝ) := ⟨0, fun μ hμ => hμ.1⟩
  obtain ⟨m, hm⟩ : ∃ m, m = sInf ({μ | InS M μ} : Set ℝ) := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by
    rw [hm]
    exact le_csInf hne (fun μ hμ => hμ.1)
  have hmS : InS M (130 * ε / 384 + 17 / 64 * m) := by
    refine ⟨by linarith, fun c => ?_⟩
    rcases (Qv_nonneg c).eq_or_lt with h0 | hpos
    · have h := hμ0.2 c
      rw [← h0, mul_zero] at h
      rw [← h0, mul_zero]
      exact h
    · have hle : (|Gd M c| / Qv c - 130 * ε / 384) * (64 / 17) ≤ m := by
        rw [hm]
        refine le_csInf hne (fun μ hμ => ?_)
        have h := (step_all M ε μ hε hμ hnet).2 c
        rw [← div_le_iff₀ hpos] at h
        linarith
      rw [← div_le_iff₀ hpos]
      linarith
  have hm_le : m ≤ 130 * ε / 384 + 17 / 64 * m := by
    have := csInf_le hbdd hmS
    rw [← hm] at this
    exact this
  intro c
  have h := hmS.2 c
  have hQ := Qv_nonneg c
  have hcoef : 130 * ε / 384 + 17 / 64 * m ≤ ε := by linarith
  calc |Gd M c| ≤ (130 * ε / 384 + 17 / 64 * m) * Qv c := h
    _ ≤ ε * Qv c := mul_le_mul_of_nonneg_right hcoef hQ

/-! ### Counting lattice points -/

theorem geom_sum_eq (N : ℕ) :
    ∑ j ∈ Finset.Icc (-(N : ℤ)) N, (1 / 2 : ℝ) ^ j.natAbs = 3 - 2 * (1 / 2) ^ N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    have hs : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hn1 : -((N : ℤ) + 1) ∉ insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hn2 : ((N : ℤ) + 1) ∉ Finset.Icc (-(N : ℤ)) N := by
      simp only [Finset.mem_Icc]
      omega
    rw [hs, Finset.sum_insert hn1, Finset.sum_insert hn2, ih]
    have h1 : (-((N : ℤ) + 1)).natAbs = N + 1 := by omega
    have h2 : ((N : ℤ) + 1).natAbs = N + 1 := by omega
    rw [h1, h2, pow_succ]
    ring

theorem geom_sum_le (N : ℕ) :
    ∑ j ∈ Finset.Icc (-(N : ℤ)) N, (1 / 2 : ℝ) ^ j.natAbs ≤ 3 := by
  rw [geom_sum_eq]
  have : (0 : ℝ) ≤ 2 * (1 / 2) ^ N := by positivity
  linarith

def net (r : ℕ) : Finset (Fin r → ℤ) :=
  (Fintype.piFinset (fun _ : Fin r => Finset.Icc (-((130 * r : ℕ) : ℤ)) ((130 * r : ℕ) : ℤ))).filter
    (fun z => ∑ a, (z a) ^ 2 ≤ 130 * (r : ℤ))

theorem mem_net {r : ℕ} (z : Fin r → ℤ) (hz : ∑ a, (z a) ^ 2 ≤ 130 * (r : ℤ)) : z ∈ net r := by
  simp only [net, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun a => ?_, hz⟩
  have h1 : (z a) ^ 2 ≤ ∑ b, (z b) ^ 2 :=
    Finset.single_le_sum (f := fun b => (z b) ^ 2) (fun b _ => sq_nonneg (z b)) (Finset.mem_univ a)
  have h2 := Int.natAbs_le_self_sq (z a)
  have h3 : z a ≤ ((z a).natAbs : ℤ) := by omega
  have h4 : -((z a).natAbs : ℤ) ≤ z a := by omega
  push_cast
  constructor <;> linarith

theorem card_net_le (r : ℕ) : ((net r).card : ℝ) ≤ (3 * 2 ^ 130 : ℝ) ^ r := by
  have hw : ∀ z ∈ net r, (1 / 2 : ℝ) ^ (130 * r) ≤ ∏ a, (1 / 2 : ℝ) ^ (z a).natAbs := by
    intro z hz
    rw [Finset.prod_pow_eq_pow_sum]
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    simp only [net, Finset.mem_filter] at hz
    have : (∑ a, ((z a).natAbs : ℤ)) ≤ 130 * r :=
      le_trans (Finset.sum_le_sum fun a _ => Int.natAbs_le_self_sq (z a)) hz.2
    exact_mod_cast this
  have hsum : ((net r).card : ℝ) * (1 / 2 : ℝ) ^ (130 * r) ≤ (3 : ℝ) ^ r := by
    calc ((net r).card : ℝ) * (1 / 2 : ℝ) ^ (130 * r)
          = ∑ _z ∈ net r, (1 / 2 : ℝ) ^ (130 * r) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ net r, ∏ a, (1 / 2 : ℝ) ^ (z a).natAbs := Finset.sum_le_sum hw
      _ ≤ ∑ z ∈ Fintype.piFinset
            (fun _ : Fin r => Finset.Icc (-((130 * r : ℕ) : ℤ)) ((130 * r : ℕ) : ℤ)),
            ∏ a, (1 / 2 : ℝ) ^ (z a).natAbs :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ = ∏ _a : Fin r, ∑ j ∈ Finset.Icc (-((130 * r : ℕ) : ℤ)) ((130 * r : ℕ) : ℤ),
            (1 / 2 : ℝ) ^ j.natAbs :=
          (Finset.prod_univ_sum
            (fun _ : Fin r => Finset.Icc (-((130 * r : ℕ) : ℤ)) ((130 * r : ℕ) : ℤ))
            (fun _ j => (1 / 2 : ℝ) ^ j.natAbs)).symm
      _ ≤ ∏ _a : Fin r, (3 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => by positivity) (fun _ _ => geom_sum_le _)
      _ = 3 ^ r := by simp
  have h2 : (1 / 2 : ℝ) ^ (130 * r) * 2 ^ (130 * r) = 1 := by
    rw [← mul_pow]; norm_num
  calc ((net r).card : ℝ) = ((net r).card : ℝ) * (1 / 2 : ℝ) ^ (130 * r) * 2 ^ (130 * r) := by
        rw [mul_assoc, h2, mul_one]
    _ ≤ 3 ^ r * 2 ^ (130 * r) := mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = (3 * 2 ^ 130) ^ r := by rw [mul_pow, pow_mul]

/-! ### An orthonormal frame of the subspace -/

theorem exists_frame {n : ℕ} (L : Submodule ℝ (Fin n → ℝ)) :
    ∃ Φ : Matrix (Fin n) (Fin (Module.finrank ℝ L)) ℝ,
      (∀ c, Qv (Φ *ᵥ c) = Qv c) ∧ (∀ c, Φ *ᵥ c ∈ L) ∧ (∀ x ∈ L, ∃ c, Φ *ᵥ c = x) := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  let L' : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    L.map (e : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  have hr : Module.finrank ℝ L' = Module.finrank ℝ L := LinearEquiv.finrank_map_eq e L
  let b : OrthonormalBasis (Fin (Module.finrank ℝ L)) ℝ L' :=
    (stdOrthonormalBasis ℝ L').reindex (finCongr hr)
  have hmem : ∀ y : EuclideanSpace ℝ (Fin n), y ∈ L' ↔ WithLp.ofLp y ∈ L := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro h
      exact ⟨WithLp.ofLp y, h, rfl⟩
  let Φ : Matrix (Fin n) (Fin (Module.finrank ℝ L)) ℝ :=
    Matrix.of (fun i a => WithLp.ofLp ((b a : L') : EuclideanSpace ℝ (Fin n)) i)
  have horth : ∀ a a', ∑ i, WithLp.ofLp ((b a : L') : EuclideanSpace ℝ (Fin n)) i *
      WithLp.ofLp ((b a' : L') : EuclideanSpace ℝ (Fin n)) i = if a = a' then 1 else 0 := by
    intro a a'
    have h := b.inner_eq_ite a a'
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [← h]
    simp only [dotProduct, Pi.star_apply, star_trivial]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hPhi : Φᵀ * Φ = 1 := by
    ext a a'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Φ, Matrix.of_apply]
    exact horth a a'
  have hform : ∀ c, Φ *ᵥ c = ∑ a, c a • WithLp.ofLp ((b a : L') : EuclideanSpace ℝ (Fin n)) := by
    intro c
    ext i
    simp only [Matrix.mulVec, dotProduct, Φ, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro c
    unfold Qv
    rw [dotProduct_mulVec]
    have h1 : (Φ *ᵥ c) ᵥ* Φ = Φᵀ *ᵥ (Φ *ᵥ c) := by
      have := Matrix.vecMul_transpose Φᵀ (Φ *ᵥ c)
      rw [Matrix.transpose_transpose] at this
      exact this
    rw [h1, Matrix.mulVec_mulVec, hPhi, Matrix.one_mulVec]
  · intro c
    rw [hform]
    exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ ((hmem _).1 (b a).2))
  · intro x hx
    obtain ⟨yL, hyL⟩ : ∃ y : L', (y : EuclideanSpace ℝ (Fin n)) = WithLp.toLp 2 x :=
      ⟨⟨WithLp.toLp 2 x, (hmem _).2 hx⟩, rfl⟩
    refine ⟨fun a => b.repr yL a, ?_⟩
    rw [hform]
    have h := congrArg (fun v : L' => WithLp.ofLp (v : EuclideanSpace ℝ (Fin n))) (b.sum_repr yL)
    simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, WithLp.ofLp_smul] at h
    rw [hyL] at h
    exact h

/-! ### Measurability -/

theorem meas_set {Ω : Type} [MeasurableSpace Ω] {n k : ℕ} (B : Ω → Matrix (Fin k) (Fin n) ℝ)
    (hB : ∀ i j, Measurable (fun ω => B ω i j)) (x : Fin n → ℝ) (C : ℝ) :
    MeasurableSet {ω | |sqNorm (B ω *ᵥ x) - sqNorm x| ≤ C} := by
  have hm : Measurable (fun ω => sqNorm (B ω *ᵥ x)) := by
    unfold sqNorm
    refine Finset.measurable_sum _ (fun i _ => ?_)
    simp only [Matrix.mulVec, dotProduct]
    exact (Finset.measurable_sum _ (fun j _ => (hB i j).mul measurable_const)).pow_const 2
  have h1 : Measurable (fun ω => |sqNorm (B ω *ᵥ x) - sqNorm x|) :=
    continuous_abs.measurable.comp (hm.sub measurable_const)
  exact measurableSet_le h1 measurable_const

end Aux_InputSparsity_Embed_lemma_8

open Aux_InputSparsity_Embed_lemma_8 in
open InputSparsity.Embed in
theorem solution :
    ∃ Ksub : ℝ, 0 < Ksub ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P] {n k : ℕ}
        (L : Submodule ℝ (Fin n → ℝ))
        (B : Ω → Matrix (Fin k) (Fin n) ℝ),
          (∀ i j, Measurable (fun ω => B ω i j)) →
          ∀ (ε δsub : ℝ), 0 < ε → 0 < δsub →
            1 ≤ Module.finrank ℝ L →
            (∀ x ∈ L,
              1 - δsub ≤ P.real
                {ω | |sqNorm (B ω *ᵥ x) - sqNorm x| ≤ ε / 6 * sqNorm x}) →
              1 - δsub * Ksub ^ Module.finrank ℝ L ≤ P.real
                {ω | ∀ x ∈ L,
                  |sqNorm (B ω *ᵥ x) - sqNorm x| ≤ ε * sqNorm x} := by
  refine ⟨3 * 2 ^ 130, by positivity, ?_⟩
  intro Ω _ P _ n k L B hB ε δ hε hδ _ hfix
  obtain ⟨Φ, hQ, hmemL, hsurj⟩ := exists_frame L
  have keyQ : ∀ c, sqNorm (Φ *ᵥ c) = Qv c := fun c => by rw [sqNorm_eq_Qv, hQ]
  have key : ∀ ω c, Gd (B ω * Φ) c = sqNorm (B ω *ᵥ (Φ *ᵥ c)) - sqNorm (Φ *ᵥ c) := by
    intro ω c
    unfold Gd
    rw [keyQ, sqNorm_eq_Qv, Matrix.mulVec_mulVec]
  let A : (Fin (Module.finrank ℝ L) → ℤ) → Set Ω := fun z =>
    {ω | |sqNorm (B ω *ᵥ (Φ *ᵥ fun a => (z a : ℝ))) - sqNorm (Φ *ᵥ fun a => (z a : ℝ))| ≤
      ε / 6 * sqNorm (Φ *ᵥ fun a => (z a : ℝ))}
  have hAmeas : ∀ z, MeasurableSet (A z) := fun z => meas_set B hB _ _
  have hAprob : ∀ z, P.real (A z)ᶜ ≤ δ := by
    intro z
    rw [MeasureTheory.measureReal_compl (hAmeas z), MeasureTheory.probReal_univ]
    have : 1 - δ ≤ P.real (A z) := hfix _ (hmemL (fun a => (z a : ℝ)))
    linarith
  have hsub : (⋂ z ∈ net (Module.finrank ℝ L), A z) ⊆
      {ω | ∀ x ∈ L, |sqNorm (B ω *ᵥ x) - sqNorm x| ≤ ε * sqNorm x} := by
    intro ω hω
    have hω' : ∀ z ∈ net (Module.finrank ℝ L), ω ∈ A z := fun z hz => Set.mem_iInter₂.mp hω z hz
    have hnet : NetHyp (B ω * Φ) ε := by
      intro z hz
      have h : |sqNorm (B ω *ᵥ (Φ *ᵥ fun a => (z a : ℝ))) - sqNorm (Φ *ᵥ fun a => (z a : ℝ))| ≤
          ε / 6 * sqNorm (Φ *ᵥ fun a => (z a : ℝ)) := hω' z (mem_net z hz)
      rw [key ω, ← keyQ]
      exact h
    have hall := final_bound (B ω * Φ) ε hε.le hnet
    rw [Set.mem_setOf_eq]
    intro x hx
    obtain ⟨c, rfl⟩ := hsurj x hx
    have h := hall c
    rw [key ω c, ← keyQ c] at h
    exact h
  have hinter : 1 - ((net (Module.finrank ℝ L)).card : ℝ) * δ ≤
      P.real (⋂ z ∈ net (Module.finrank ℝ L), A z) := by
    have hmeasI : MeasurableSet (⋂ z ∈ net (Module.finrank ℝ L), A z) :=
      Finset.measurableSet_biInter _ (fun z _ => hAmeas z)
    have h1 := MeasureTheory.measureReal_compl (μ := P) hmeasI
    rw [MeasureTheory.probReal_univ, Set.compl_iInter₂] at h1
    have h2 : P.real (⋃ z ∈ net (Module.finrank ℝ L), (A z)ᶜ) ≤
        ∑ z ∈ net (Module.finrank ℝ L), P.real (A z)ᶜ :=
      MeasureTheory.measureReal_biUnion_finset_le _ _
    have h3 : ∑ z ∈ net (Module.finrank ℝ L), P.real (A z)ᶜ ≤
        ∑ _z ∈ net (Module.finrank ℝ L), δ := Finset.sum_le_sum (fun z _ => hAprob z)
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    linarith
  have hcard := card_net_le (Module.finrank ℝ L)
  have hcd := mul_le_mul_of_nonneg_left hcard hδ.le
  calc 1 - δ * (3 * 2 ^ 130) ^ Module.finrank ℝ L
        ≤ 1 - ((net (Module.finrank ℝ L)).card : ℝ) * δ := by linarith
    _ ≤ P.real (⋂ z ∈ net (Module.finrank ℝ L), A z) := hinter
    _ ≤ _ := MeasureTheory.measureReal_mono hsub
