-- Prove2me | solution 1 for IoTFusion.KnownQuality.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:26:19.615993+00:00
-- url     : https://prove2.me/submissions/bd9d6f6c-be0d-458a-9a2f-cc3e8fc77562

import Mathlib
import Definitions.Def_IoTFusion_KnownQuality_Model
import Theorems.Thm_IoTFusion_KnownQuality_proposition_2

open IoTFusion.KnownQuality

theorem solution {n : ℕ} (P : IoTFusion.KnownQuality.Instance n) (hq : ∀ i, 0 < P.q i)
    (hv : ∀ i j, 0 < P.v i j) (hw : ∀ i j, 0 < P.w i j) :
    ∀ ε : ℝ, 0 < ε → ∃ ψbar : ℝ, ∀ (s : ℕ → ℝ) (i j j' : Fin n) (k : ℕ), j ≠ i → j' ≠ i →
      ψbar < fam P i s k j (s k) → 1 + ε < P.q j / P.q j' → target P i s k ≠ j' := by
  intro ε hε
  set e : ℝ := 2 * ε + ε ^ 2 with he
  have hepos : 0 < e := by positivity
  refine ⟨∑ m : Fin n, 1 / (P.q m ^ 2 * e), ?_⟩
  intro s i j j' k hji hj'i hψ hrat htar
  -- positivity of familiarities
  have hfampos : ∀ m : Fin n, 0 < fam P i s k m (s k) := by
    intro m
    rw [(proposition_2 P i m s (s k)).2 k]
    have h1 : 0 < psi1 P i m (s k) := by
      unfold psi1; have := hv i m; have := hw i m; positivity
    have h2 : 0 ≤ stick (P.q i) (P.q m) := by
      unfold stick; have := hq i; have := hq m; positivity
    positivity
  -- the threshold term for j
  have hTj : 1 / (P.q j ^ 2 * e) ≤ ∑ m : Fin n, 1 / (P.q m ^ 2 * e) :=
    Finset.single_le_sum (f := fun m => 1 / (P.q m ^ 2 * e))
      (fun m _ => by have := hq m; positivity) (Finset.mem_univ j)
  -- j' is a minimizer
  set c : Fin n → ℝ := fun m => sigma2 (P.q m) (fam P i s k m (s k)) with hc
  have hmin : c j' ≤ c j := by
    have ht : target P i s k = lowArgmin i c := rfl
    rw [ht] at htar
    unfold lowArgmin at htar
    split_ifs at htar with hne
    · have hmem := Finset.min'_mem _ hne
      rw [htar] at hmem
      unfold minimizersExcept at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem.2 j hji
    · exact absurd htar.symm hj'i
  -- now the algebra
  have ha := hq j
  have hb := hq j'
  set a := P.q j
  set b := P.q j'
  set ψ := fam P i s k j (s k)
  set ψ' := fam P i s k j' (s k)
  have hψ'pos : 0 < ψ' := hfampos j'
  have hψj : 1 / (a ^ 2 * e) < ψ := lt_of_le_of_lt hTj hψ
  have hab : (1 + ε) * b < a := by rwa [lt_div_iff₀ hb] at hrat
  have hψpos : 0 < ψ := hfampos j
  have hcj : c j = 1 / a ^ 2 + (1 / ψ) / a ^ 4 := by
    show sigma2 a ψ = _
    unfold sigma2; field_simp
  have hcj' : c j' = 1 / b ^ 2 + (1 / ψ') / b ^ 4 := by
    show sigma2 b ψ' = _
    unfold sigma2; field_simp
  have hinv : 1 / ψ < a ^ 2 * e := by
    have hpos : 0 < 1 / (a ^ 2 * e) := by positivity
    rw [div_lt_iff₀ (by linarith)]
    rw [div_lt_iff₀ (by positivity)] at hψj
    nlinarith
  have hA : c j < (1 + ε) ^ 2 / a ^ 2 := by
    rw [hcj]
    have : (1 / ψ) / a ^ 4 < (a ^ 2 * e) / a ^ 4 := by
      apply div_lt_div_of_pos_right hinv (by positivity)
    have h2 : (a ^ 2 * e) / a ^ 4 = e / a ^ 2 := by field_simp
    have h3 : (1 + ε) ^ 2 / a ^ 2 = 1 / a ^ 2 + e / a ^ 2 := by
      rw [he]; field_simp; ring
    linarith
  have hB : (1 + ε) ^ 2 / a ^ 2 < 1 / b ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have h1 : 0 < (1 + ε) * b := by positivity
    nlinarith
  have hC : 1 / b ^ 2 < c j' := by
    rw [hcj']
    have : 0 < (1 / ψ') / b ^ 4 := by positivity
    linarith
  linarith
