-- Prove2me | solution 1 for MNLTrisection.Adaptive.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:03:23.362029+00:00
-- url     : https://prove2.me/submissions/9a503f47-934d-4b63-aa0c-3b8cbd126c02

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTriAux

open MNLTrisection.Adaptive MNLBandit.UCB ChoiceCDLP.MNL Filter Topology

variable {N : ℕ}

theorem rev_def (v r : Fin N → ℝ) (S : Finset (Fin N)) :
    rev v r S = (∑ j ∈ S, r j * v j) / (∑ j ∈ S, v j + 1) := by
  simp [rev, mnlObjective, mul_comm]

theorem den_pos (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) :
    0 < ∑ j ∈ S, v j + 1 := by
  have := Finset.sum_nonneg (fun j (_ : j ∈ S) => hv j); linarith

theorem sum_shift (v r : Fin N → ℝ) (S : Finset (Fin N)) (θ : ℝ) :
    ∑ j ∈ S, (r j - θ) * v j = ∑ j ∈ S, r j * v j - θ * ∑ j ∈ S, v j := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem le_rev_iff (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) (θ : ℝ) :
    θ ≤ rev v r S ↔ θ ≤ ∑ j ∈ S, (r j - θ) * v j := by
  rw [rev_def, le_div_iff₀ (den_pos v hv S), sum_shift]
  constructor <;> intro h <;> linarith

theorem rev_le_iff (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) (θ : ℝ) :
    rev v r S ≤ θ ↔ ∑ j ∈ S, (r j - θ) * v j ≤ θ := by
  rw [rev_def, div_le_iff₀ (den_pos v hv S), sum_shift]
  constructor <;> intro h <;> linarith

theorem sum_le_level (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) (θ : ℝ) :
    ∑ j ∈ S, (r j - θ) * v j ≤ ∑ j ∈ levelSet r θ, (r j - θ) * v j := by
  calc ∑ j ∈ S, (r j - θ) * v j ≤ ∑ j ∈ S.filter (fun j => θ ≤ r j), (r j - θ) * v j := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro j _
        split_ifs with h
        · exact le_rfl
        · push Not at h
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hv j)
    _ ≤ ∑ j ∈ levelSet r θ, (r j - θ) * v j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_filter] at hj
          simp [levelSet, hj.2]
        · intro j hj _
          simp only [levelSet, Finset.mem_filter] at hj
          exact mul_nonneg (by linarith [hj.2]) (hv j)

theorem exists_opt (v r : Fin N → ℝ) :
    ∃ S : Finset (Fin N), ∀ S' : Finset (Fin N), rev v r S' ≤ rev v r S := by
  obtain ⟨S, -, hS⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin N)))
    (rev v r) ⟨∅, Finset.mem_univ _⟩
  exact ⟨S, fun S' => hS S' (Finset.mem_univ _)⟩

theorem optRev_eq (v r : Fin N → ℝ) (S : Finset (Fin N))
    (hS : ∀ S' : Finset (Fin N), rev v r S' ≤ rev v r S) : optRev v r = rev v r S := by
  unfold optRev optRevenue
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun S' _ => hS S')
  · exact Finset.le_sup' (fun S => mnlObjective v r 1 S) (Finset.mem_univ S)

theorem rev_empty (v r : Fin N → ℝ) : rev v r ∅ = 0 := by simp [rev, mnlObjective]

theorem rev_le_optRev (v r : Fin N → ℝ) (S : Finset (Fin N)) : rev v r S ≤ optRev v r := by
  obtain ⟨S0, hS0⟩ := exists_opt v r
  rw [optRev_eq v r S0 hS0]; exact hS0 S

theorem optRev_nonneg (v r : Fin N → ℝ) : 0 ≤ optRev v r := by
  have := rev_le_optRev v r ∅; rwa [rev_empty] at this

/-- The optimal revenue is a fixed point of `F`. -/
theorem F_optRev (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) : F v r (optRev v r) = optRev v r := by
  obtain ⟨S0, hS0⟩ := exists_opt v r
  have hR := optRev_eq v r S0 hS0
  apply le_antisymm (rev_le_optRev v r _)
  show optRev v r ≤ rev v r (levelSet r (optRev v r))
  rw [le_rev_iff v r hv]
  have h1 : optRev v r ≤ rev v r S0 := hR.le
  rw [le_rev_iff v r hv] at h1
  exact h1.trans (sum_le_level v r hv S0 _)

theorem Fstar_eq (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) : Fstar v r = optRev v r := by
  unfold Fstar
  apply IsGreatest.csSup_eq
  refine ⟨⟨optRev v r, optRev_nonneg v r, F_optRev v r hv⟩, ?_⟩
  rintro _ ⟨θ, -, rfl⟩
  exact rev_le_optRev v r _

theorem thetaStar_eq (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) : thetaStar v r = optRev v r :=
  Fstar_eq v r hv

theorem sum_filter_split (r g : Fin N → ℝ) (θ : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => θ ≤ r i), g i =
      ∑ i ∈ Finset.univ.filter (fun i => θ < r i), g i +
        ∑ i ∈ Finset.univ.filter (fun i => r i = θ), g i := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases lt_trichotomy θ (r i) with h | h | h
  · simp [h, h.le, h.ne']
  · simp [h]
  · simp [not_le.mpr h, not_lt.mpr h.le, h.ne]

theorem rightLim_F (v r : Fin N → ℝ) (θ : ℝ) :
    Function.rightLim (F v r) θ = rev v r (Finset.univ.filter (fun i => θ < r i)) := by
  apply rightLim_eq_of_tendsto
  have key : ∀ i : Fin N, ∀ᶠ y in 𝓝[>] θ, (y ≤ r i ↔ θ < r i) := by
    intro i
    by_cases h : θ < r i
    · have : ∀ᶠ y in 𝓝[>] θ, y < r i := nhdsWithin_le_nhds (Iio_mem_nhds h)
      filter_upwards [this] with y hy
      exact ⟨fun _ => h, fun _ => hy.le⟩
    · push Not at h
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : θ < y := hy
      exact ⟨fun h' => by linarith, fun h' => by linarith⟩
  have hall := Filter.eventually_all.2 key
  apply tendsto_const_nhds.congr'
  filter_upwards [hall] with y hy
  unfold F levelSet
  congr 1
  ext i
  simp [hy i]

theorem jump_identity (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (θ : ℝ) :
    F v r θ - rev v r (Finset.univ.filter (fun i => θ < r i)) =
      (∑ i ∈ Finset.univ.filter (fun i => r i = θ), v i) /
          (1 + ∑ i ∈ Finset.univ.filter (fun i => θ ≤ r i), v i) *
        (θ - rev v r (Finset.univ.filter (fun i => θ < r i))) := by
  unfold F levelSet
  rw [rev_def, rev_def, sum_filter_split r (fun i => r i * v i) θ,
    sum_filter_split r v θ]
  have he : ∑ i ∈ Finset.univ.filter (fun i => r i = θ), r i * v i =
      θ * ∑ i ∈ Finset.univ.filter (fun i => r i = θ), v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter] at hi
    rw [hi.2]
  rw [he]
  set A := ∑ i ∈ Finset.univ.filter (fun i => θ < r i), r i * v i
  set B := ∑ i ∈ Finset.univ.filter (fun i => θ < r i), v i
  set V := ∑ i ∈ Finset.univ.filter (fun i => r i = θ), v i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hv i)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i _ => hv i)
  have h1 : (B + 1) ≠ 0 := by positivity
  have h2 : (B + V + 1) ≠ 0 := by positivity
  have h3 : (1 + (B + V)) ≠ 0 := by positivity
  field_simp
  ring

theorem jump_coef_nonneg (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (θ : ℝ) :
    0 ≤ (∑ i ∈ Finset.univ.filter (fun i => r i = θ), v i) /
          (1 + ∑ i ∈ Finset.univ.filter (fun i => θ ≤ r i), v i) := by
  apply div_nonneg (Finset.sum_nonneg (fun i _ => hv i))
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ.filter (fun i => θ ≤ r i)) => hv i)
  linarith

theorem le_F_of_le (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (θ : ℝ) (hθ : θ ≤ optRev v r) :
    θ ≤ F v r θ := by
  obtain ⟨S0, hS0⟩ := exists_opt v r
  have hR := optRev_eq v r S0 hS0
  have h1 : optRev v r ≤ rev v r S0 := hR.le
  rw [le_rev_iff v r hv] at h1
  unfold F
  rw [le_rev_iff v r hv]
  refine le_trans ?_ (sum_le_level v r hv S0 θ)
  have hsplit : ∑ j ∈ S0, (r j - θ) * v j =
      ∑ j ∈ S0, (r j - optRev v r) * v j + (optRev v r - θ) * ∑ j ∈ S0, v j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hVs : 0 ≤ ∑ j ∈ S0, v j := Finset.sum_nonneg (fun j _ => hv j)
  rw [hsplit]
  nlinarith

theorem le_rev_strict_of_le (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (θ : ℝ)
    (hθ : θ ≤ optRev v r) : θ ≤ rev v r (Finset.univ.filter (fun i => θ < r i)) := by
  have h := le_F_of_le v r hv θ hθ
  unfold F levelSet at h
  rw [le_rev_iff v r hv] at h ⊢
  rw [sum_filter_split r (fun j => (r j - θ) * v j) θ] at h
  have h0 : ∑ i ∈ Finset.univ.filter (fun i => r i = θ), (r i - θ) * v i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter] at hi
    simp [hi.2]
  linarith

end MNLTriAux

namespace MNLTriPol

open MNLTrisection.Adaptive MNLBandit.UCB ChoiceCDLP.MNL

variable {N : ℕ}

theorem step_props (r : Fin N → ℝ) (T : ℕ) (s : AlgState) (c : Option (Fin N))
    (hs : s.a ≤ s.b) :
    (step r T s c).a ≤ (step r T s c).b ∧ s.a ≤ (step r T s c).a ∧
      (step r T s c).b ≤ s.b ∧ s.tau ≤ (step r T s c).tau := by
  unfold step
  split_ifs
  · exact ⟨hs, le_rfl, le_rfl, le_rfl⟩
  · simp only [epochStart, AlgState.y]
    refine ⟨?_, le_rfl, ?_, Nat.le_succ _⟩ <;> linarith
  · simp only [epochStart, AlgState.x]
    refine ⟨?_, ?_, le_rfl, Nat.le_succ _⟩ <;> linarith
  · exact ⟨hs, le_rfl, le_rfl, le_rfl⟩

theorem fold_props (r : Fin N → ℝ) (T : ℕ) (l : List (Option (Fin N))) :
    ∀ s : AlgState, s.a ≤ s.b →
      (l.foldl (step r T) s).a ≤ (l.foldl (step r T) s).b ∧ s.a ≤ (l.foldl (step r T) s).a ∧
      (l.foldl (step r T) s).b ≤ s.b ∧ s.tau ≤ (l.foldl (step r T) s).tau := by
  induction l with
  | nil => intro s hs; simp [hs]
  | cons c l ih =>
    intro s hs
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := step_props r T s c hs
    obtain ⟨g1, g2, g3, g4⟩ := ih _ h1
    exact ⟨g1, h2.trans g2, g3.trans h3, h4.trans g4⟩

theorem ofFn_prefix {T : ℕ} (h : History N T) (t : Fin T) :
    List.ofFn (histPrefix h t) = (List.ofFn h).take t := by
  apply List.ext_getElem
  · simp [t.isLt.le]
  · intro n h1 h2
    simp [histPrefix, List.getElem_ofFn, List.getElem_take]

theorem stateOf_eq {T : ℕ} (r : Fin N → ℝ) (h : History N T) (t : Fin T) :
    stateOf r h t = ((List.ofFn h).take t).foldl (step r T) initState := by
  unfold stateOf stateAt
  rw [ofFn_prefix]

theorem stateOf_mono {T : ℕ} (r : Fin N → ℝ) (h : History N T) (t1 t2 : Fin T)
    (h12 : t1 ≤ t2) :
    (stateOf r h t2).a ≤ (stateOf r h t2).b ∧ (stateOf r h t1).a ≤ (stateOf r h t2).a ∧
      (stateOf r h t2).b ≤ (stateOf r h t1).b ∧ (stateOf r h t1).tau ≤ (stateOf r h t2).tau := by
  have hsplit : (List.ofFn h).take t2 =
      (List.ofFn h).take t1 ++ ((List.ofFn h).take t2).drop t1 := by
    conv_lhs => rw [← List.take_append_drop (t1 : ℕ) ((List.ofFn h).take t2)]
    rw [List.take_take, min_eq_left (by exact_mod_cast h12)]
  rw [stateOf_eq r h t2, hsplit, List.foldl_append, ← stateOf_eq r h t1]
  have h0 : (stateOf r h t1).a ≤ (stateOf r h t1).b := by
    rw [stateOf_eq]
    exact (fold_props r T _ initState (by simp [initState, epochStart])).1
  exact fold_props r T _ _ h0

theorem histProb_nonneg {T : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N)
    (h : History N T) : 0 ≤ histProb v π h := by
  unfold histProb
  apply Finset.prod_nonneg
  intro t _
  have hd : 0 < 1 + ∑ j ∈ offered π h t, v j := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ offered π h t) => hv j); linarith
  cases hc : h t with
  | none => simp only [choiceProb]; positivity
  | some i =>
    simp only [choiceProb]
    split_ifs
    · exact div_nonneg (hv i) hd.le
    · exact le_rfl

theorem regret_case3_pointwise {T : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (τ : ℕ)
    (α β : ℝ) (h : History N T) (hC : Cond v r 3 τ α β h) (t : Fin T)
    (ht : τ ≤ epochOf r h t) :
    optRev v r - rev v r (offered (adaptivePolicy r T) h t) ≤ α := by
  classical
  obtain ⟨⟨hst, hev⟩, hα, -⟩ := hC
  have hev3 : epochA r h τ < epochB r h τ ∧ epochB r h τ < thetaStar v r := by
    rcases hev with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
    · norm_num at h1
    · norm_num at h1
    · exact h2
  have hne : (epochTimes r h τ).Nonempty := by
    obtain ⟨t', ht'⟩ := hst
    exact ⟨t', by simp [epochTimes, ht']⟩
  set t0 := (epochTimes r h τ).min' hne with ht0
  have hA : epochA r h τ = (stateOf r h t0).a := by
    simp [epochA, epochState, hne, ht0]
  have hB : epochB r h τ = (stateOf r h t0).b := by
    simp [epochB, epochState, hne, ht0]
  have ht0mem : t0 ∈ epochTimes r h τ := Finset.min'_mem _ _
  have ht0e : epochOf r h t0 = τ := by simpa [epochTimes] using ht0mem
  have hle : t0 ≤ t := by
    by_contra hlt
    push Not at hlt
    have := (stateOf_mono r h t t0 hlt.le).2.2.2
    have heq : epochOf r h t = τ := by
      unfold epochOf at ht ht0e ⊢; omega
    have hmem : t ∈ epochTimes r h τ := by simp [epochTimes, heq]
    have := Finset.min'_le _ _ hmem
    rw [← ht0] at this
    exact absurd hlt (not_lt.mpr this)
  obtain ⟨m1, m2, m3, -⟩ := stateOf_mono r h t0 t hle
  rw [MNLTriAux.thetaStar_eq v r hv] at hev3
  rw [MNLTriAux.thetaStar_eq v r hv] at hα
  set s := stateOf r h t
  have hoff : offered (adaptivePolicy r T) h t = offerOf r s := rfl
  rw [hoff]
  have hlev : ∃ θ, offerOf r s = levelSet r θ ∧ s.a ≤ θ ∧ θ ≤ s.b := by
    unfold offerOf
    split_ifs
    · exact ⟨s.y, rfl, by simp only [AlgState.y]; linarith, by simp only [AlgState.y]; linarith⟩
    · exact ⟨s.a, rfl, le_rfl, m1⟩
  obtain ⟨θ, hθ, hθ1, hθ2⟩ := hlev
  rw [hθ]
  have hθle : θ ≤ optRev v r := by linarith
  have hF := MNLTriAux.le_F_of_le v r hv θ hθle
  have hFdef : F v r θ = rev v r (levelSet r θ) := rfl
  rw [abs_of_neg (by linarith)] at hα
  linarith

end MNLTriPol

open MNLTrisection.Adaptive MNLBandit.UCB in
theorem solution {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (T τ : ℕ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    psi v r T 3 τ α β ≤ α * T := by
  classical
  -- pointwise bound on the regret to go
  have hpt : ∀ h : History N T, Cond v r 3 τ α β h → regretToGo v r h τ ≤ α * T := by
    intro h hC
    unfold regretToGo
    calc ∑ τ' ∈ Finset.Icc τ (tau0 r h), ∑ t ∈ epochTimes r h τ',
          (optRev v r - rev v r (offered (adaptivePolicy r T) h t))
        ≤ ∑ τ' ∈ Finset.Icc τ (tau0 r h), ∑ t ∈ epochTimes r h τ', α := by
          apply Finset.sum_le_sum
          intro τ' hτ'
          apply Finset.sum_le_sum
          intro t ht
          have he : epochOf r h t = τ' := by simpa [epochTimes] using ht
          apply MNLTriPol.regret_case3_pointwise v r hv τ α β h hC t
          rw [he]; exact (Finset.mem_Icc.mp hτ').1
      _ = α * ∑ τ' ∈ Finset.Icc τ (tau0 r h), ((epochTimes r h τ').card : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro τ' _
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ α * T := by
          apply mul_le_mul_of_nonneg_left _ hα
          have hcard : ∑ τ' ∈ Finset.Icc τ (tau0 r h), (epochTimes r h τ').card =
              ((Finset.Icc τ (tau0 r h)).biUnion (epochTimes r h)).card := by
            rw [Finset.card_biUnion]
            intro x _ y _ hxy
            simp only [Function.onFun, epochTimes]
            exact Finset.disjoint_filter.mpr (fun t _ h1 h2 => hxy (h1.symm.trans h2))
          have hle : ((Finset.Icc τ (tau0 r h)).biUnion (epochTimes r h)).card ≤ T := by
            calc _ ≤ (Finset.univ : Finset (Fin T)).card := Finset.card_le_univ _
              _ = T := by simp
          rw [← Nat.cast_sum, hcard]
          exact_mod_cast hle
  unfold psi probT
  set D := ∑ h : History N T, if Cond v r 3 τ α β h then histProb v (adaptivePolicy r T) h else 0
  have hD : 0 ≤ D := Finset.sum_nonneg (fun h _ => by
    split_ifs
    · exact MNLTriPol.histProb_nonneg v hv _ h
    · exact le_rfl)
  rcases hD.eq_or_lt with hD0 | hDpos
  · rw [← hD0, div_zero]; positivity
  · rw [div_le_iff₀ hDpos, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    split_ifs with hC
    · have := hpt h hC
      have hp := MNLTriPol.histProb_nonneg v hv (adaptivePolicy r T) h
      nlinarith
    · simp
