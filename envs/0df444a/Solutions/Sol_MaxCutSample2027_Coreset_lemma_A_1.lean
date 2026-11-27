-- Prove2me | solution 1 for MaxCutSample2027.Coreset.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:24:35.582607+00:00
-- url     : https://prove2.me/submissions/4c9723d8-d743-498e-b8e7-05a2e77f8c66

import Definitions.Def_MaxCutSample2027_Coreset_signed
open scoped BigOperators

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset

private noncomputable def opt {E : Type*} (T : Set E) (f : E → ℝ) : ℝ := sSup (f '' T)

private theorem opt_spec {E : Type*} [TopologicalSpace E] {T : Set E} (hne : T.Nonempty)
    (hT : IsCompact T) {f : E → ℝ} (hf : Continuous f) :
    (∃ t ∈ T, f t = opt T f) ∧ ∀ t ∈ T, f t ≤ opt T f := by
  have upper (t : E) (ht : t ∈ T) : f t ≤ opt T f :=
    le_csSup (hT.image hf).bddAbove ⟨t, ht, rfl⟩
  obtain ⟨t, ht, hm⟩ := hT.exists_isMaxOn hne hf.continuousOn
  exact ⟨⟨t, ht, le_antisymm (upper t ht) (csSup_le (hne.image _) (by
    rintro _ ⟨z, hz, rfl⟩; exact hm hz))⟩, upper⟩

private def score {k : ℕ} (φ : Fin k → ℝ → ℝ) (σ : Fin k → Bool) (t : Fin k → ℝ) : ℝ :=
  ∑ i, signValue (σ i) * φ i (t i)

private theorem score_continuous {k : ℕ} {φ : Fin k → ℝ → ℝ}
    (hφ : ∀ i, Continuous (φ i)) (σ : Fin k → Bool) : Continuous (score φ σ) := by
  unfold score
  fun_prop

private theorem sign_flip_value (b : Bool) : signValue (!b) = -signValue b := by cases b <;> norm_num [signValue]
private theorem abs_sign_value (b : Bool) : |signValue b| = 1 := by cases b <;> norm_num [signValue]

private def flipCoord {k : ℕ} (i : Fin k) (σ : Fin k → Bool) : Fin k → Bool :=
  Function.update σ i (!σ i)

private theorem flipCoord_involutive {k : ℕ} (i : Fin k) : Function.Involutive (flipCoord i) := by
  intro σ
  funext j
  by_cases h : j = i
  · subst j; simp [flipCoord]
  · simp [flipCoord, Function.update_of_ne h]

private theorem one_coordinate {k : ℕ} {T : Set (Fin k → ℝ)} (hne : T.Nonempty) (hT : IsCompact T)
    (i : Fin k) (φ : Fin k → ℝ → ℝ) (hφ : ∀ i, Continuous (φ i))
    (lip : ∀ a b, |φ i a - φ i b| ≤ |a - b|) :
    (∑ σ, opt T (score φ σ)) ≤ ∑ σ, opt T (score (Function.update φ i id) σ) := by
  let ψ := Function.update φ i id
  have hψ (j : Fin k) : Continuous (ψ j) := by
    by_cases h : j = i
    · subst j; simpa [ψ] using continuous_id
    · simpa [ψ, Function.update_of_ne h] using hφ j
  have pair_bound (σ : Fin k → Bool) : opt T (score φ σ) + opt T (score φ (flipCoord i σ)) ≤
      opt T (score ψ σ) + opt T (score ψ (flipCoord i σ)) := by
    obtain ⟨a, ha, hmax_a⟩ := (opt_spec hne hT (score_continuous hφ σ)).1
    obtain ⟨b, hb, hmax_b⟩ := (opt_spec hne hT (score_continuous hφ (flipCoord i σ))).1
    let rest (t : Fin k → ℝ) := ∑ j ∈ Finset.univ.erase i, signValue (σ j) * φ j (t j)
    let s := signValue (σ i)
    have score_old (t : Fin k → ℝ) : score φ σ t = rest t + s * φ i (t i) := by
      unfold score
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
    have score_old_flip (t : Fin k → ℝ) : score φ (flipCoord i σ) t = rest t - s * φ i (t i) := by
      unfold score
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      have h : (∑ j ∈ Finset.univ.erase i, signValue (flipCoord i σ j) * φ j (t j)) = rest t := by
        exact Finset.sum_congr rfl fun j hj => by simp [flipCoord, Function.update_of_ne (Finset.mem_erase.mp hj).1]
      rw [h]
      simp [flipCoord, sign_flip_value, s, sub_eq_add_neg]
    have score_new (t : Fin k → ℝ) : score ψ σ t = rest t + s * t i := by
      unfold score
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      have h : (∑ j ∈ Finset.univ.erase i, signValue (σ j) * ψ j (t j)) = rest t := by
        exact Finset.sum_congr rfl fun j hj => by simp [ψ, Function.update_of_ne (Finset.mem_erase.mp hj).1]
      rw [h]
      simp [ψ, s]
    have score_new_flip (t : Fin k → ℝ) : score ψ (flipCoord i σ) t = rest t - s * t i := by
      unfold score
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      have h : (∑ j ∈ Finset.univ.erase i, signValue (flipCoord i σ j) * ψ j (t j)) = rest t := by
        exact Finset.sum_congr rfl fun j hj => by
          simp [ψ, flipCoord, Function.update_of_ne (Finset.mem_erase.mp hj).1]
      rw [h]
      simp [ψ, flipCoord, sign_flip_value, s, sub_eq_add_neg]
    have bound_left (t : Fin k → ℝ) (ht : t ∈ T) := (opt_spec hne hT (score_continuous hψ σ)).2 t ht
    have bound_right (t : Fin k → ℝ) (ht : t ∈ T) := (opt_spec hne hT (score_continuous hψ (flipCoord i σ))).2 t ht
    have step : s * (φ i (a i) - φ i (b i)) ≤ |s * (a i - b i)| := by
      calc
        _ ≤ |s * (φ i (a i) - φ i (b i))| := le_abs_self _
        _ ≤ _ := by simp only [abs_mul, s, abs_sign_value, one_mul]; exact lip _ _
    calc
      _ = rest a + rest b + s * (φ i (a i) - φ i (b i)) := by
        rw [← hmax_a, ← hmax_b, score_old, score_old_flip]
        ring
      _ ≤ rest a + rest b + |s * (a i - b i)| := add_le_add le_rfl step
      _ ≤ _ := by
        by_cases hs : 0 ≤ s * (a i - b i)
        · rw [abs_of_nonneg hs]
          have h₁ := bound_left a ha
          have h₂ := bound_right b hb
          rw [score_new] at h₁
          rw [score_new_flip] at h₂
          linarith
        · rw [abs_of_nonpos (le_of_not_ge hs)]
          have h₁ := bound_left b hb
          have h₂ := bound_right a ha
          rw [score_new] at h₁
          rw [score_new_flip] at h₂
          linarith
  let perm : (Fin k → Bool) ≃ (Fin k → Bool) :=
    ⟨flipCoord i, flipCoord i, flipCoord_involutive i, flipCoord_involutive i⟩
  have perm_sum (f : (Fin k → Bool) → ℝ) : (∑ σ, f (flipCoord i σ)) = ∑ σ, f σ :=
    Fintype.sum_equiv perm _ _ fun _ => rfl
  have h := Finset.sum_le_sum (s := Finset.univ) (fun σ _ => pair_bound σ)
  simp only [Finset.sum_add_distrib] at h
  rw [perm_sum (fun σ => opt T (score φ σ)), perm_sum (fun σ => opt T (score ψ σ))] at h
  change (∑ σ, opt T (score φ σ)) ≤ ∑ σ, opt T (score ψ σ)
  linarith

theorem solution (k : ℕ) (hk : 1 ≤ k)
    (T : Set (Fin k → ℝ)) (hT : T.Nonempty) (hcompact : IsCompact T)
    (g : ℝ → ℝ) (hg : LipschitzWith 1 g) (hg0 : g 0 = 0) :
    signAverage k (contractionMaximum T g) ≤
      2 * signAverage k (contractionMaximum T (fun t => t)) := by
  classical
  let U := insert 0 T
  have hU : IsCompact U := hcompact.insert _
  have hUne : U.Nonempty := ⟨0, Set.mem_insert _ _⟩
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have gdist (x y : ℝ) : |g x - g y| ≤ |x - y| := by
    simpa [Real.dist_eq] using hg.dist_le_mul x y
  have score_neg (φ : Fin k → ℝ → ℝ) (σ : Fin k → Bool) (t : Fin k → ℝ) :
      score φ (fun i => !σ i) t = -score φ σ t := by
    simp only [score, sign_flip_value, neg_mul, Finset.sum_neg_distrib]
  have pair_sum (f : (Fin k → Bool) → ℝ) : (∑ σ : Fin k → Bool, f (fun i => !σ i)) = ∑ σ, f σ := by
    let flip (σ : Fin k → Bool) : Fin k → Bool := fun i => !σ i
    have invol : Function.Involutive flip := by intro σ; funext i; simp [flip]
    let perm : (Fin k → Bool) ≃ (Fin k → Bool) := ⟨flip, flip, invol, invol⟩
    exact Fintype.sum_equiv perm _ _ fun _ => rfl
  have abs_le_pair (σ : Fin k → Bool) :
      opt T (fun t => |score (fun _ => g) σ t|) ≤
        opt U (score (fun _ => g) σ) + opt U (score (fun _ => g) (fun i => !σ i)) := by
    have old := opt_spec hT hcompact ((score_continuous (fun _ => hg.continuous) σ).abs)
    obtain ⟨t, ht, hmax⟩ := old.1
    rw [← hmax]
    have direct := (opt_spec hUne hU (score_continuous (fun _ => hg.continuous) σ)).2
    have flipped := (opt_spec hUne hU (score_continuous (fun _ => hg.continuous) (fun i => !σ i))).2
    have score_zero (τ : Fin k → Bool) : score (fun _ => g) τ 0 = 0 := by simp [score, hg0]
    have hpos := direct 0 (Set.mem_insert _ _)
    have hneg := flipped 0 (Set.mem_insert _ _)
    rw [score_zero] at hpos hneg
    have htu : t ∈ U := Set.mem_insert_of_mem _ ht
    by_cases h : 0 ≤ score (fun _ => g) σ t
    · rw [abs_of_nonneg h]
      linarith [direct t htu]
    · rw [abs_of_nonpos (le_of_not_ge h)]
      have hh := flipped t htu
      rw [score_neg] at hh
      linarith
  have first : (∑ σ, opt T (fun t => |score (fun _ => g) σ t|)) ≤
      2 * ∑ σ, opt U (score (fun _ => g) σ) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun σ _ => abs_le_pair σ)
    simp only [Finset.sum_add_distrib] at h
    rw [pair_sum (fun σ => opt U (score (fun _ => g) σ))] at h
    linarith
  let φ (s : Finset (Fin k)) (i : Fin k) : ℝ → ℝ := if i ∈ s then id else g
  have replace (s : Finset (Fin k)) : (∑ σ, opt U (score (fun _ => g) σ)) ≤
      ∑ σ, opt U (score (φ s) σ) := by
    induction s using Finset.induction_on with
    | empty => simp [φ]
    | @insert i s hi ih =>
      apply ih.trans
      have hcont (j : Fin k) : Continuous (φ s j) := by
        by_cases hj : j ∈ s
        · simpa only [φ, if_pos hj] using (continuous_id : Continuous (id : ℝ → ℝ))
        · simpa only [φ, if_neg hj] using hg.continuous
      have hl a b : |φ s i a - φ s i b| ≤ |a - b| := by simpa [φ, hi] using gdist a b
      have upd : Function.update (φ s) i id = φ (insert i s) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [φ]
        · simp [φ, hj]
      rw [← upd]
      exact one_coordinate hUne hU i (φ s) hcont hl
  have second : (∑ σ, opt U (score (fun _ => g) σ)) ≤ ∑ σ, opt U (score (fun _ => id) σ) := by
    simpa only [φ, Finset.mem_univ, if_true] using replace Finset.univ
  have third (σ : Fin k → Bool) : opt U (score (fun _ => id) σ) ≤
      opt T (fun t => |score (fun _ => id) σ t|) := by
    obtain ⟨t, ht, hmax⟩ := (opt_spec hUne hU (score_continuous (fun _ => continuous_id) σ)).1
    rw [← hmax]
    have hbound := (opt_spec hT hcompact ((score_continuous (fun _ => continuous_id) σ).abs)).2
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · obtain ⟨s, hs⟩ := hT
      have hs' := hbound s hs
      simpa [score] using (abs_nonneg _).trans hs'
    · exact (le_abs_self _).trans (hbound t ht)
  have all : (∑ σ, opt T (fun t => |score (fun _ => g) σ t|)) ≤
      2 * ∑ σ, opt T (fun t => |score (fun _ => id) σ t|) := by
    refine first.trans (mul_le_mul_of_nonneg_left (second.trans ?_) (by norm_num))
    exact Finset.sum_le_sum fun σ _ => third σ
  have normalized (f : ℝ → ℝ) (hf : Continuous f) (σ : Fin k → Bool) :
      contractionMaximum T f σ = opt T (fun t => |score (fun _ => f) σ t|) / (k : ℝ) := by
    unfold contractionMaximum
    simp only [abs_div, abs_of_pos hkreal]
    change opt T (fun t => |score (fun _ => f) σ t| / (k : ℝ)) = _
    have cont := (score_continuous (fun _ => hf) σ).abs
    have h₁ := opt_spec hT hcompact cont
    have h₂ := opt_spec hT hcompact (cont.div_const (k : ℝ))
    obtain ⟨a, ha, hmax₁⟩ := h₁.1
    obtain ⟨b, hb, hmax₂⟩ := h₂.1
    exact le_antisymm (hmax₂ ▸ div_le_div_of_nonneg_right (h₁.2 b hb) hkreal.le)
      (hmax₁ ▸ h₂.2 a ha)
  change signAverage k (contractionMaximum T g) ≤ 2 * signAverage k (contractionMaximum T id)
  unfold signAverage
  simp only [normalized g hg.continuous, normalized id continuous_id, ← Finset.sum_div]
  have h := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right all hkreal.le)
    (show 0 ≤ (2 : ℝ) ^ k by positivity)
  convert h using 1 <;> first | rfl | ring
