-- Prove2me | solution 1 for NOFSeparation750.CodedGIP.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:28:26.620011+00:00
-- url     : https://prove2.me/submissions/439d6f9d-a574-4e68-9b0c-824558c8f916
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_NOFSeparation750_CodedGIP_theorem_3_2
import Theorems.Thm_NOFSeparation750_CodedGIP_theorem_4_1
import Theorems.Thm_NOFSeparation750_CodedGIP_theorem_5_1
import Theorems.Thm_NOFSeparation750_CodedGIP_padded_uniformPolyTime

open NOFSeparation750.CodedGIP Finset

namespace MainAux

def comapTree {k : ℕ} {X Y : Fin k → Type} (g : ∀ i, Y i → X i) :
    BitProtocol X → BitProtocol Y
  | .leaf b => .leaf b
  | .send i f p₀ p₁ => .send i (fun v => f (fun j => g j.val (v j))) (comapTree g p₀) (comapTree g p₁)

theorem run_comap {k : ℕ} {X Y : Fin k → Type} (g : ∀ i, Y i → X i) :
    ∀ (P : BitProtocol X) (y : Input Y), (comapTree g P).run y = P.run (fun i => g i (y i))
  | .leaf b, y => rfl
  | .send i f p₀ p₁, y => by
      simp only [comapTree, BitProtocol.run, run_comap g p₀, run_comap g p₁]
      rfl

theorem exists_allowed (k : ℕ) (hk : 1 ≤ k) : ∃ a, Allowed k a := by
  set N := (32 * k) ^ 2 with hN
  have hN1 : 1 < N := by
    have : 32 ≤ 32 * k := by omega
    have : 32 ^ 2 ≤ N := Nat.pow_le_pow_left this 2
    omega
  refine ⟨Nat.clog 4 N, ?_, Nat.le_pow_clog (by norm_num) N, ?_⟩
  · exact Nat.clog_pos (by norm_num) (by omega)
  · have h1 := Nat.pow_pred_clog_lt_self (b := 4) (by norm_num) hN1
    have hpos : 0 < Nat.clog 4 N := Nat.clog_pos (by norm_num) (by omega)
    have : 4 ^ Nat.clog 4 N = 4 * 4 ^ (Nat.clog 4 N).pred := by
      rw [← pow_succ']; congr 1; rw [Nat.pred_eq_sub_one]; omega
    rw [this]
    have h64 : (64 * k) ^ 2 = 4 * N := by rw [hN]; ring
    omega

theorem codeLength_succ (a j : ℕ) : codeLength a (j + 1) = codeLength a j * 2 ^ a := by
  unfold codeLength; ring

theorem envelope_succ (k a j : ℕ) : envelope k a (j + 1) = envelope k a j * 2 ^ a := by
  unfold envelope; rw [codeLength_succ]; ring

theorem lt_envelope (k a n : ℕ) (ha : 1 ≤ a) : n < envelope k a n := by
  unfold envelope codeLength
  have h1 : 1 ≤ 4 ^ a - 2 ^ a := by
    have : 2 ^ a < 4 ^ a := Nat.pow_lt_pow_left (by norm_num) (by omega)
    omega
  have h2 : n < (2 ^ a) ^ n := by
    calc n < 2 ^ n := Nat.lt_two_pow_self
      _ ≤ (2 ^ a) ^ n := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2 |>.trans' le_rfl) n
  have h3 : 1 ≤ (copies k + 1) := by omega
  have h4 : 1 ≤ 2 * a := by omega
  calc n < (2 ^ a) ^ n := h2
    _ ≤ (4 ^ a - 2 ^ a) * (2 ^ a) ^ n := Nat.le_mul_of_pos_left _ h1
    _ ≤ (copies k + 1) * ((4 ^ a - 2 ^ a) * (2 ^ a) ^ n) := Nat.le_mul_of_pos_left _ h3
    _ ≤ (copies k + 1) * ((4 ^ a - 2 ^ a) * (2 ^ a) ^ n) * (2 * a) := Nat.le_mul_of_pos_right _ h4

theorem paddingLevel_spec (k a n : ℕ) (ha : 1 ≤ a) (hn : envelope k a 0 ≤ n) :
    envelope k a (paddingLevel k a n) ≤ n ∧ paddingLevel k a n ≤ n ∧
      n < envelope k a (paddingLevel k a n + 1) ∧
      (∀ j, j ≤ n → envelope k a j ≤ n → j ≤ paddingLevel k a n) := by
  classical
  set S := (range (n + 1)).filter (fun j => envelope k a j ≤ n) with hS
  have h0 : 0 ∈ S := by simp [hS, hn]
  have hne : S.Nonempty := ⟨0, h0⟩
  have hpl : paddingLevel k a n = S.max' hne := by
    unfold paddingLevel
    rw [← hS, ← Finset.coe_max' hne]; rfl
  have hmem := S.max'_mem hne
  rw [← hpl] at hmem
  simp only [hS, mem_filter, mem_range] at hmem
  have hmax : ∀ j, j ≤ n → envelope k a j ≤ n → j ≤ paddingLevel k a n := by
    intro j hj he
    rw [hpl]; exact S.le_max' j (by simp [hS]; omega)
  refine ⟨hmem.2, by omega, ?_, hmax⟩
  by_contra hcon
  push Not at hcon
  by_cases hj : paddingLevel k a n + 1 ≤ n
  · have := hmax _ hj hcon; omega
  · have hpn : paddingLevel k a n = n := by omega
    have := lt_envelope k a (n + 1) ha
    rw [hpn] at hcon
    omega

end MainAux

open MainAux in
theorem solution (k : ℕ) (hk : 3 ≤ k) :
    ∃ F : BooleanFamily k, UniformPolyTime F ∧
      ∃ C : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        (∃ P : PublicProtocol (fun _ : Fin k => Bits n),
          P.Bounded C ∧ P.OneSided (F n) (1 / 3)) ∧
        (∀ P : NondetProtocol (fun _ : Fin k => Bits n), ∀ d : ℕ,
          P.Correct (F n) → P.Bounded d → c * (n : ℝ) ≤ d) := by
  classical
  obtain ⟨a, ha⟩ := exists_allowed k (by omega)
  have ha1 := ha.1
  let K := GaloisField 2 (2 * a)
  let _ : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = 4 ^ a := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * a) (by omega), pow_mul]; norm_num
  obtain ⟨D, codec, hcomp, heff⟩ := theorem_3_2 k a (by omega) ha K hK
  obtain ⟨c5, hc5, j₀, h51⟩ := theorem_5_1 k (by omega)
  refine ⟨paddedFamily D codec k, padded_uniformPolyTime k a (by omega) ha K D codec heff,
    (copies k + 1) * (2 * a) + 1, c5 * (3 / ((64 * k : ℕ) : ℝ) ^ 2), by positivity,
    envelope k a 0 + envelope k a j₀ + j₀, ?_⟩
  intro n hn
  have hn0 : envelope k a 0 ≤ n := by omega
  obtain ⟨hU, hjn, hUs, hmax⟩ := paddingLevel_spec k a n ha1 hn0
  have hjj : j₀ ≤ paddingLevel k a n := hmax j₀ (by omega) (by omega)
  set j := paddingLevel k a n with hj
  set ℓ := copies k with hℓ
  set N := nativeLength (D j) ℓ (2 * a) with hN
  set m := (D j).small.dimension with hm
  set mt := (D j).large.dimension with hmt
  have hmr : m ≤ codeLength a j := by
    have := Submodule.finrank_le (D j).small.code
    rwa [Module.finrank_eq_card_basis (D j).small.basis, Fintype.card_fin,
      Module.finrank_fin_fun] at this
  have hmtr : mt ≤ codeLength a j := by
    have := Submodule.finrank_le (D j).large.code
    rwa [Module.finrank_eq_card_basis (D j).large.basis, Fintype.card_fin,
      Module.finrank_fin_fun] at this
  have hNU : N ≤ envelope k a j := by
    rw [hN, nativeLength, envelope, ← hℓ]
    apply Nat.mul_le_mul_right
    calc ℓ * m + mt ≤ ℓ * codeLength a j + codeLength a j :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hmr) hmtr
      _ = (ℓ + 1) * codeLength a j := by ring
  have hNn : N ≤ n := hNU.trans hU
  let π : Bits n → Bits N := fun x t => (List.ofFn x).getD t.val false
  have hFam : ∀ x, paddedFamily D codec k n x = nativeFunction (D j) codec ℓ k (fun i => π (x i)) := by
    intro x
    unfold paddedFamily
    rw [if_neg (by omega)]
  constructor
  · obtain ⟨P, hPb, hP1, hP0⟩ := theorem_4_1 k ℓ (codeLength a j) (2 * a) (by omega)
      (6 / 2 ^ a) K (D j) codec (hcomp j)
    have hacc : ∀ y : Input (fun _ : Fin k => Bits n),
        (∑ s, if ((comapTree (fun _ => π) (P.tree s)).run y).1 then P.weight s else 0) =
          P.acceptance (fun i => π (y i)) := by
      intro y; simp only [run_comap]; rfl
    refine ⟨⟨P.seeds, P.weight, P.nonneg, P.total, fun s => comapTree (fun _ => π) (P.tree s)⟩,
      ?_, ?_, ?_⟩
    · intro s y
      rw [run_comap]; exact hPb s _
    · intro y hy
      rw [hFam] at hy
      exact (hacc y).trans (hP1 _ hy)
    · intro y hy
      rw [hFam] at hy
      exact ((hacc y).trans_le (hP0 _ hy)).trans (by norm_num)
  · intro P d hP hd
    let e : Bits N → Bits n := fun x t => if h : t.val < N then x ⟨t.val, h⟩ else false
    have hπe : ∀ x, π (e x) = x := by
      intro x; funext t
      have ht : t.val < n := lt_of_lt_of_le t.2 hNn
      simp only [π]
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp [e, t.2]
    let P' : NondetProtocol (fun _ : Fin k => Bits N) :=
      ⟨P.certificateBits, fun z => comapTree (fun _ => e) (P.verifier z)⟩
    have hP' : P'.Correct (nativeFunction (D j) codec ℓ k) := by
      intro x
      have := hP (fun i => e (x i))
      rw [hFam] at this
      simp only [hπe] at this
      rw [this]
      simp only [P', run_comap]
    have hd' : P'.Bounded d := by
      obtain ⟨c0, hc0, hv⟩ := hd
      refine ⟨c0, hc0, fun z x => ?_⟩
      simp only [P', run_comap]
      exact hv z _
    have h5 := h51 a ha K D codec hcomp j hjj P' d hP' hd'
    -- N is at least a fixed fraction of n
    obtain ⟨-, hr1, -, -, -, -, -, -, hdimV, -⟩ := hcomp j
    set s := 2 ^ a with hs
    have hfrV : Module.finrank K (D j).small.code = m := by
      rw [Module.finrank_eq_card_basis (D j).small.basis, Fintype.card_fin]
    have hspos : (0:ℝ) < (s:ℝ) := by exact_mod_cast (show 0 < s by positivity)
    have h6r : 6 * codeLength a j ≤ s * m := by
      rw [hfrV] at hdimV
      have : (6 * codeLength a j : ℝ) ≤ s * m := by
        have h' := mul_le_mul_of_nonneg_left hdimV hspos.le
        rw [show ((2:ℝ) ^ a) = (s : ℝ) by rw [hs]; push_cast; ring] at h'
        rw [← mul_assoc, mul_div_cancel₀ _ hspos.ne'] at h'
        linarith
      exact_mod_cast this
    have hs64 : s ≤ 64 * k := by
      have hq4 : (4 : ℕ) ^ a = s * s := by rw [hs, ← mul_pow]; norm_num
      have : s ^ 2 ≤ (64 * k) ^ 2 := by rw [sq, ← hq4]; exact ha.2.2
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
    have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; unfold copies; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hkey : 3 * n < s * s * N := by
      rw [envelope_succ, ← hs] at hUs
      have e1 : envelope k a j = (ℓ + 1) * codeLength a j * (2 * a) := rfl
      have e2 : N = (ℓ * m + mt) * (2 * a) := rfl
      -- s * N ≥ 3 * envelope
      have h3 : 3 * envelope k a j ≤ s * N := by
        rw [e1, e2]
        have hA : 3 * ((ℓ + 1) * codeLength a j) ≤ ℓ * (6 * codeLength a j) := by nlinarith
        have hB : ℓ * (6 * codeLength a j) ≤ s * (ℓ * m + mt) := by
          calc ℓ * (6 * codeLength a j) ≤ ℓ * (s * m) := Nat.mul_le_mul_left _ h6r
            _ = s * (ℓ * m) := by ring
            _ ≤ s * (ℓ * m + mt) := Nat.mul_le_mul_left _ (by omega)
        calc 3 * ((ℓ + 1) * codeLength a j * (2 * a))
            = 3 * ((ℓ + 1) * codeLength a j) * (2 * a) := by ring
          _ ≤ s * (ℓ * m + mt) * (2 * a) := Nat.mul_le_mul_right _ (hA.trans hB)
          _ = s * ((ℓ * m + mt) * (2 * a)) := by ring
      calc 3 * n < 3 * (envelope k a j * s) := by omega
        _ = s * (3 * envelope k a j) := by ring
        _ ≤ s * (s * N) := Nat.mul_le_mul_left _ h3
        _ = s * s * N := by ring
    have hkey' : (3 : ℝ) * n ≤ ((64 * k : ℕ) : ℝ) ^ 2 * N := by
      have h1 : (3 : ℝ) * n ≤ (s:ℝ) * s * N := by exact_mod_cast hkey.le
      have h2 : (s : ℝ) ≤ ((64 * k : ℕ) : ℝ) := by exact_mod_cast hs64
      have hN0 : (0:ℝ) ≤ N := by positivity
      calc (3:ℝ) * n ≤ (s:ℝ) * s * N := h1
        _ ≤ ((64 * k : ℕ) : ℝ) * ((64 * k : ℕ) : ℝ) * N := by gcongr
        _ = ((64 * k : ℕ) : ℝ) ^ 2 * N := by ring
    have h64 : (0:ℝ) < ((64 * k : ℕ) : ℝ) ^ 2 := by positivity
    calc c5 * (3 / ((64 * k : ℕ) : ℝ) ^ 2) * n = c5 * ((3 * n) / ((64 * k : ℕ) : ℝ) ^ 2) := by ring
      _ ≤ c5 * N := by
          gcongr
          rw [div_le_iff₀ h64]; linarith
      _ ≤ d := h5
