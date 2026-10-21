-- Prove2me | solution 1 for ModernOnlineLearning.ToX.theorem_16_4
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T05:54:49.899977+00:00
-- url     : https://prove2.me/submissions/d8ccabc7-b2ec-4c99-9b74-75f61ffc1160

import Definitions.Def_ModernOnlineLearning_ToX_Algorithms
open ModernOnlineLearning.ToX

private lemma flip_sum_zero {T : ℕ} (t : Round T) (F : (Round T → Bool) → ℝ)
    (hF : ∀ ε, F (Function.update ε t (!(ε t))) = F ε) :
    (∑ ε : Round T → Bool, sign ε t * F ε) = 0 := by
  classical
  let flip : (Round T → Bool) → (Round T → Bool) := fun ε => Function.update ε t (!(ε t))
  have hinv : Function.Involutive flip := by
    intro ε
    funext s
    by_cases hs : s = t
    · subst s
      simp [flip]
    · simp [flip, Function.update_of_ne hs]
  let e : (Round T → Bool) ≃ (Round T → Bool) := ⟨flip, flip, hinv, hinv⟩
  have he := e.sum_comp (fun ε => sign ε t * F ε)
  have hterm (ε : Round T → Bool) : sign (e ε) t * F (e ε) = -(sign ε t * F ε) := by
    change sign (flip ε) t * F (flip ε) = _
    rw [hF ε]
    dsimp [flip, sign]
    simp only [Function.update_self]
    cases ε t <;> simp
  simp_rw [hterm] at he
  rw [Finset.sum_neg_distrib] at he
  linarith

theorem solution {d T : ℕ} (hT : 1 ≤ T)
    (Z V : Set (Fin d → ℝ)) (z : ℕ → Fin d → ℝ)
    (hZsym : ∀ a ∈ Z, -a ∈ Z)
    (hz : ∀ t ∈ Finset.Icc 1 T, z t ∈ Z)
    (hVne : V.Nonempty) (hVbd : Bornology.IsBounded V) (hVclosed : IsClosed V)
    (R : ℕ → ℝ) (A : (ℕ → Fin d → ℝ) → ℕ → Fin d → ℝ)
    (hA : IsOnlineAlgorithm T Z V (R T) A) :
    empiricalRadLinear (T := T) V hT ⟨hVne, hVbd⟩ z ≤ R T / (T : ℝ) := by
  classical
  let grad : (Round T → Bool) → ℕ → Fin d → ℝ := fun ε s =>
    if hs : s ∈ Finset.Icc 1 T then fun i => -sign ε ⟨s,hs⟩ * z s i else 0
  have hgrad (ε : Round T → Bool) : ∀ s ∈ Finset.Icc 1 T, grad ε s ∈ Z := by
    intro s hs
    dsimp [grad]
    rw [dif_pos hs]
    unfold sign
    split_ifs
    · simp only [neg_mul, one_mul]
      exact hZsym (z s) (hz s hs)
    · simpa using hz s hs
  have hpair (ε : Round T → Bool) (t : Round T) (v : Fin d → ℝ) :
      pairing (grad ε t) v = -sign ε t * pairing v (z t) := by
    simp only [grad, dif_pos t.property]
    simp only [pairing, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsup (ε : Round T → Bool) : signedLinearSup V ⟨hVne,hVbd⟩ z ε ≤
      R T + ∑ t : Round T, sign ε t * pairing (A (grad ε) t) (z t) := by
    unfold signedLinearSup
    apply csSup_le
    · obtain ⟨u, hu⟩ := hVne
      exact ⟨_, u, hu, rfl⟩
    · rintro a ⟨u, hu, rfl⟩
      have hr := (hA.2 (grad ε) (hgrad ε)).2 u hu
      rw [← Finset.sum_coe_sort (Finset.Icc 1 T)] at hr
      change (∑ t : Round T, (pairing (grad ε t) (A (grad ε) t) - pairing (grad ε t) u)) ≤ R T at hr
      simp only [hpair] at hr
      have halg : (∑ t : Round T, (-sign ε t * pairing (A (grad ε) t) (z t) - -sign ε t * pairing u (z t))) =
          (∑ t : Round T, sign ε t * pairing u (z t)) -
            ∑ t : Round T, sign ε t * pairing (A (grad ε) t) (z t) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro t ht
        ring
      rw [halg] at hr
      linarith
  have hzero (t : Round T) :
      (∑ ε : Round T → Bool, sign ε t * pairing (A (grad ε) t) (z t)) = 0 := by
    apply flip_sum_zero t
    intro ε
    have ha : A (grad (Function.update ε t (!(ε t)))) t = A (grad ε) t := by
      apply hA.1 _ _ t t.property
      intro s hs
      obtain ⟨hs1,hst⟩ := Finset.mem_Ico.mp hs
      have hsT : s ∈ Finset.Icc 1 T := by
        obtain ⟨ht1,htT⟩ := Finset.mem_Icc.mp t.property
        exact Finset.mem_Icc.mpr ⟨hs1, by omega⟩
      have hne : (⟨s,hsT⟩ : Round T) ≠ t := by
        intro h
        have hv : s = t.val := congrArg Subtype.val h
        omega
      funext i
      simp only [grad, dif_pos hsT, sign, Function.update_of_ne hne]
    rw [ha]
  have hsumzero : (∑ ε : Round T → Bool, ∑ t : Round T,
      sign ε t * pairing (A (grad ε) t) (z t)) = 0 := by
    rw [Finset.sum_comm]
    simp only [hzero, Finset.sum_const_zero]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun ε _ => hsup ε)
  rw [Finset.sum_add_distrib, hsumzero, add_zero] at hs
  have hcard : Fintype.card (Round T → Bool) = 2^T := by simp [Fintype.card_fun, Round]
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hs
  have hTpos : 0 < (T:ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hscale := mul_le_mul_of_nonneg_left hs (show 0 ≤ (1/(T:ℝ))*(1/(2:ℝ)^T) by positivity)
  change empiricalRadLinear (T := T) V hT ⟨hVne,hVbd⟩ z ≤ _ at hscale
  convert hscale using 1
  field_simp

