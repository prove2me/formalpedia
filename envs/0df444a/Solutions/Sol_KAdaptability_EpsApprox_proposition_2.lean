-- Prove2me | solution 1 for KAdaptability.EpsApprox.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:14:12.548246+00:00
-- url     : https://prove2.me/submissions/de9f65f7-ff99-4231-89a4-e65ff39ea948

import Mathlib
import Definitions.Def_KAdaptability_EpsApprox_Approx

namespace RRAux_KAdaptability_EpsApprox_proposition_2

open Matrix KAdaptability.EpsApprox KAdaptability.EpsApprox.Problem

-- uniformize a "for all sufficiently small ε" property over a finite set
theorem uniform_small {α : Type*} {D : Set α} (hD : D.Finite) (Q : α → ℝ → Prop)
    (h : ∀ d ∈ D, ∃ e > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) e, Q d ε) :
    ∃ e > 0, ∀ d ∈ D, ∀ ε ∈ Set.Ioc (0 : ℝ) e, Q d ε := by
  induction D, hD using Set.Finite.induction_on with
  | empty => exact ⟨1, one_pos, fun d hd => absurd hd (Set.notMem_empty d)⟩
  | @insert a s _ _ ih =>
    obtain ⟨e1, he1, h1⟩ := h a (Set.mem_insert a s)
    obtain ⟨e2, he2, h2⟩ := ih (fun d hd => h d (Set.mem_insert_of_mem a hd))
    refine ⟨min e1 e2, lt_min he1 he2, fun d hd ε hε => ?_⟩
    rcases Set.mem_insert_iff.1 hd with rfl | hd
    · exact h1 ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
    · exact h2 d hd ε ⟨hε.1, hε.2.trans (min_le_right _ _)⟩

variable {N M L nQ R K : ℕ} (P : Problem N M L nQ R)

theorem decisions_finite :
    {d : (Fin N → ℝ) × (Fin K → Fin M → ℝ) | P.IsDecision d.1 d.2}.Finite := by
  have hX : {x : Fin N → ℝ | ∀ i, x i = 0 ∨ x i = 1}.Finite := by
    refine (Set.finite_range (fun b : Fin N → Bool => fun i => if b i then (1 : ℝ) else 0)).subset ?_
    intro x hx
    refine ⟨fun i => decide (x i = 1), funext fun i => ?_⟩
    rcases hx i with h | h <;> simp [h]
  have hY : {y : Fin K → Fin M → ℝ | ∀ k, y k ∈ P.Y}.Finite := by
    refine (Set.finite_range (fun f : Fin K → P.Y => fun k => (f k).1)).subset ?_
    intro y hy
    exact ⟨fun k => ⟨y k, hy k⟩, rfl⟩
  refine (hX.prod hY).subset ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact ⟨P.X_binary x hx, hy⟩

theorem XiEps_sub (ε : ℝ) (hε : 0 < ε) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ)
    (ℓ : Fin K → Fin (L + 1)) : P.XiEps ε x y ℓ ⊆ P.XiL x y ℓ := by
  rintro ξ ⟨h1, h2, h3⟩
  exact ⟨h1, h2, fun k i hk => by linarith [h3 k i hk]⟩

theorem obj6Eps_le (ε : ℝ) (hε : 0 < ε) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) :
    P.obj6Eps ε x y ≤ P.obj6 x y := by
  unfold obj6Eps obj6
  exact iSup_mono fun ℓ => biSup_mono fun ξ hξ => XiEps_sub P ε hε x y ℓ hξ

theorem margin (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (ξ : EuclideanSpace ℝ (Fin nQ)) (hξ : ξ ∈ P.XiL x y ℓ) :
    ∃ e > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) e, ξ ∈ P.XiEps ε x y ℓ := by
  obtain ⟨h1, h2, h3⟩ := hξ
  obtain ⟨e, he, hall⟩ := uniform_small (Set.finite_univ (α := Fin K × Fin L))
    (fun p ε => ℓ p.1 = p.2.succ → P.rhs ξ p.2 + ε ≤ P.lhs x (y p.1) p.2) (by
      rintro ⟨k, i⟩ -
      by_cases hk : ℓ k = i.succ
      · have := h3 k i hk
        refine ⟨P.lhs x (y k) i - P.rhs ξ i, by linarith, fun ε hε _ => ?_⟩
        linarith [hε.2]
      · exact ⟨1, one_pos, fun ε _ hk' => absurd hk' hk⟩)
  exact ⟨e, he, fun ε hε => ⟨h1, h2, fun k i hk => hall (k, i) (Set.mem_univ _) ε hε hk⟩⟩

-- Claim A: anything strictly below obj6 is strictly below obj6Eps for small ε
theorem claimA (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (b : EReal) (hb : b < P.obj6 x y) :
    ∃ e > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) e, b < P.obj6Eps ε x y := by
  unfold obj6 at hb
  obtain ⟨ℓ, hℓ⟩ := lt_iSup_iff.1 hb
  obtain ⟨ξ, hξ⟩ := lt_iSup_iff.1 hℓ
  obtain ⟨hξL, hlt⟩ := lt_iSup_iff.1 hξ
  obtain ⟨e, he, hm⟩ := margin P x y ℓ ξ hξL
  refine ⟨e, he, fun ε hε => ?_⟩
  unfold obj6Eps
  exact lt_of_lt_of_le hlt (le_iSup_of_le ℓ (le_iSup₂_of_le ξ (hm ε hε) le_rfl))

theorem dot_le (ξ : Fin nQ → ℝ) (r : ℝ) (hr : ∀ i, |ξ i| ≤ r) (v : Fin nQ → ℝ) :
    ξ ⬝ᵥ v ≤ r * ∑ i, |v i| := by
  unfold dotProduct
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ξ i * v i ≤ |ξ i * v i| := le_abs_self _
    _ = |ξ i| * |v i| := abs_mul _ _
    _ ≤ r * |v i| := mul_le_mul_of_nonneg_right (hr i) (abs_nonneg _)

-- Lemma B: on Ξ every bracket is either ⊤ or below a fixed real bound
theorem claimB (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) :
    ∃ U : ℝ, ∀ ℓ ξ, ξ ∈ P.Xi → P.bracket x y ℓ ξ ≤ U ∨ P.bracket x y ℓ ξ = ⊤ := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin nQ → ℝ)).1 P.Xi_bounded
  have hco : ∀ ξ ∈ P.Xi, ∀ i, |ξ.ofLp i| ≤ r := by
    intro ξ hξ i
    have h := hr hξ
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact (norm_le_pi_norm ξ.ofLp i).trans h
  refine ⟨r * ∑ i, |(P.C *ᵥ x) i| + ∑ k, r * ∑ i, |(P.Q *ᵥ y k) i|, fun ℓ ξ hξ => ?_⟩
  by_cases hz : ∃ k0, ℓ k0 = 0
  · left
    obtain ⟨k0, hk0⟩ := hz
    unfold bracket
    have h1 : (⨅ k ∈ {k : Fin K | ℓ k = 0}, ((P.secondCost ξ (y k) : ℝ) : EReal)) ≤
        ((P.secondCost ξ (y k0) : ℝ) : EReal) := iInf₂_le k0 hk0
    have h2 : P.firstCost ξ x ≤ r * ∑ i, |(P.C *ᵥ x) i| := dot_le _ r (hco ξ hξ) _
    have h3 : P.secondCost ξ (y k0) ≤ ∑ k, r * ∑ i, |(P.Q *ᵥ y k) i| := by
      refine (dot_le _ r (hco ξ hξ) _).trans ?_
      refine Finset.single_le_sum (f := fun k => r * ∑ i, |(P.Q *ᵥ y k) i|) (fun k _ => ?_)
        (Finset.mem_univ k0)
      have : 0 ≤ r := Metric.nonempty_closedBall.1 ⟨_, hr P.Xi_nonempty.some_mem⟩
      exact mul_nonneg this (Finset.sum_nonneg fun i _ => abs_nonneg _)
    calc ((P.firstCost ξ x : ℝ) : EReal) + ⨅ k ∈ {k : Fin K | ℓ k = 0},
          ((P.secondCost ξ (y k) : ℝ) : EReal)
        ≤ ((P.firstCost ξ x : ℝ) : EReal) + ((P.secondCost ξ (y k0) : ℝ) : EReal) :=
          add_le_add_right h1 _
      _ = ((P.firstCost ξ x + P.secondCost ξ (y k0) : ℝ) : EReal) := by norm_cast
      _ ≤ _ := EReal.coe_le_coe_iff.2 (by linarith)
  · right
    push Not at hz
    unfold bracket
    have : (⨅ k ∈ {k : Fin K | ℓ k = 0}, ((P.secondCost ξ (y k) : ℝ) : EReal)) = ⊤ :=
      iInf₂_eq_top.2 fun k hk => absurd hk (hz k)
    rw [this, EReal.coe_add_top]

theorem bracket_lower (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (ξ : EuclideanSpace ℝ (Fin nQ)) : ⊥ < P.bracket x y ℓ ξ := by
  unfold bracket
  have h : (((-∑ k, |P.secondCost ξ (y k)| : ℝ)) : EReal) ≤
      ⨅ k ∈ {k : Fin K | ℓ k = 0}, ((P.secondCost ξ (y k) : ℝ) : EReal) := by
    refine le_iInf₂ fun k _ => EReal.coe_le_coe_iff.2 ?_
    have := Finset.single_le_sum (f := fun k => |P.secondCost ξ (y k)|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ k)
    have := neg_abs_le (P.secondCost ξ (y k))
    try simp only at *
    linarith
  calc (⊥ : EReal) < (((P.firstCost ξ x + -∑ k, |P.secondCost ξ (y k)|) : ℝ) : EReal) :=
        EReal.bot_lt_coe _
    _ = ((P.firstCost ξ x : ℝ) : EReal) + (((-∑ k, |P.secondCost ξ (y k)| : ℝ)) : EReal) := by
        norm_cast
    _ ≤ _ := add_le_add_right h _

theorem obj6_ne_bot (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) : ⊥ < P.obj6 x y := by
  obtain ⟨ξ0', hξ0'⟩ := P.Xi_nonempty
  let ξ0 : EuclideanSpace ℝ (Fin nQ) := WithLp.toLp 2 ξ0'
  have hξ0 : ξ0 ∈ P.Xi := hξ0'
  classical
  let ℓ0 : Fin K → Fin (L + 1) := fun k =>
    if h : P.lhs x (y k) ≤ P.rhs ξ0 then 0
    else (Classical.choose (by
      simpa [Pi.le_def, not_forall, not_le] using h :
        ∃ i, P.rhs ξ0 i < P.lhs x (y k) i)).succ
  have hmem : ξ0 ∈ P.XiL x y ℓ0 := by
    refine ⟨hξ0, fun k hk => ?_, fun k i hk => ?_⟩
    · by_contra h
      simp only [ℓ0, dif_neg h] at hk
      exact Fin.succ_ne_zero _ hk
    · by_cases h : P.lhs x (y k) ≤ P.rhs ξ0
      · simp only [ℓ0, dif_pos h] at hk
        exact absurd hk.symm (Fin.succ_ne_zero _)
      · simp only [ℓ0, dif_neg h] at hk
        have hi := Fin.succ_injective _ hk
        have hs := Classical.choose_spec (by
          simpa [Pi.le_def, not_forall, not_le] using h :
            ∃ i, P.rhs ξ0 i < P.lhs x (y k) i)
        rw [hi] at hs
        exact hs
  unfold obj6
  exact lt_of_lt_of_le (bracket_lower P x y ℓ0 ξ0)
    (le_iSup_of_le ℓ0 (le_iSup₂_of_le ξ0 hmem le_rfl))

end RRAux_KAdaptability_EpsApprox_proposition_2

open KAdaptability.EpsApprox in
open Problem in
theorem solution {N M L nQ R : ℕ} (P : Problem N M L nQ R) (K : ℕ) :
    (∃ ε₀ > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε₀, P.dom6Eps K ε = P.dom6 K) ∧
    (∀ κ > 0, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε₀, ∀ d ∈ P.dom6 K,
      ∃ φ φε : ℝ, P.obj6 d.1 d.2 = (φ : EReal) ∧ P.obj6Eps ε d.1 d.2 = (φε : EReal) ∧
        |φε - φ| ≤ κ) := by
  open RRAux_KAdaptability_EpsApprox_proposition_2 in
  constructor
  · obtain ⟨e, he, h⟩ := uniform_small (decisions_finite P (K := K))
      (fun d ε => P.obj6Eps ε d.1 d.2 < ⊤ → P.obj6 d.1 d.2 < ⊤) (by
        intro d _
        by_cases htop : P.obj6 d.1 d.2 < ⊤
        · exact ⟨1, one_pos, fun _ _ _ => htop⟩
        · have htop' : P.obj6 d.1 d.2 = ⊤ := not_lt_top_iff.1 htop
          obtain ⟨U, hU⟩ := claimB P d.1 d.2
          obtain ⟨e, he, hA⟩ := claimA P d.1 d.2 (U : EReal) (by rw [htop']; exact EReal.coe_lt_top U)
          refine ⟨e, he, fun ε hε hlt => ?_⟩
          exfalso
          have h1 := hA ε hε
          unfold obj6Eps at h1 hlt
          obtain ⟨ℓ, hℓ⟩ := lt_iSup_iff.1 h1
          obtain ⟨ξ, hξ⟩ := lt_iSup_iff.1 hℓ
          obtain ⟨hξE, hlt'⟩ := lt_iSup_iff.1 hξ
          rcases hU ℓ ξ hξE.1 with hle | heq
          · exact absurd hle (not_le.2 hlt')
          · have : (⊤ : EReal) ≤ ⨆ ℓ, ⨆ ξ ∈ P.XiEps ε d.1 d.2 ℓ, P.bracket d.1 d.2 ℓ ξ :=
              heq ▸ le_iSup_of_le ℓ (le_iSup₂_of_le ξ hξE le_rfl)
            exact absurd hlt (not_lt.2 this))
    refine ⟨e, he, fun ε hε => ?_⟩
    ext d
    constructor
    · rintro ⟨hd, hlt⟩
      exact ⟨hd, h d hd ε hε hlt⟩
    · rintro ⟨hd, hlt⟩
      exact ⟨hd, lt_of_le_of_lt (obj6Eps_le P ε hε.1 d.1 d.2) hlt⟩
  · intro κ hκ
    obtain ⟨e, he, h⟩ := uniform_small (decisions_finite P (K := K))
      (fun d ε => d ∈ P.dom6 K → ∃ φ φε : ℝ, P.obj6 d.1 d.2 = (φ : EReal) ∧
        P.obj6Eps ε d.1 d.2 = (φε : EReal) ∧ |φε - φ| ≤ κ) (by
        intro d _
        by_cases hdom : d ∈ P.dom6 K
        · have hne_top : P.obj6 d.1 d.2 ≠ ⊤ := hdom.2.ne
          have hne_bot : P.obj6 d.1 d.2 ≠ ⊥ := (obj6_ne_bot P d.1 d.2).ne'
          set φ := (P.obj6 d.1 d.2).toReal with hφdef
          have hφ : P.obj6 d.1 d.2 = (φ : EReal) := (EReal.coe_toReal hne_top hne_bot).symm
          obtain ⟨e, he, hA⟩ := claimA P d.1 d.2 ((φ - κ : ℝ) : EReal)
            (by rw [hφ]; exact EReal.coe_lt_coe_iff.2 (by linarith))
          refine ⟨e, he, fun ε hε _ => ?_⟩
          have hlo := hA ε hε
          have hhi : P.obj6Eps ε d.1 d.2 ≤ (φ : EReal) := hφ ▸ obj6Eps_le P ε hε.1 d.1 d.2
          have hne_top' : P.obj6Eps ε d.1 d.2 ≠ ⊤ :=
            (lt_of_le_of_lt hhi (EReal.coe_lt_top φ)).ne
          have hne_bot' : P.obj6Eps ε d.1 d.2 ≠ ⊥ :=
            (lt_trans (EReal.bot_lt_coe _) hlo).ne'
          have hφε := (EReal.coe_toReal hne_top' hne_bot').symm
          refine ⟨φ, (P.obj6Eps ε d.1 d.2).toReal, hφ, hφε, ?_⟩
          rw [hφε] at hlo hhi
          have h1 := EReal.coe_lt_coe_iff.1 hlo
          have h2 := EReal.coe_le_coe_iff.1 hhi
          rw [abs_le]
          constructor <;> linarith
        · exact ⟨1, one_pos, fun _ _ h => absurd h hdom⟩)
    exact ⟨e, he, fun ε hε d hd => h d hd.1 ε hε hd⟩

#print axioms solution
