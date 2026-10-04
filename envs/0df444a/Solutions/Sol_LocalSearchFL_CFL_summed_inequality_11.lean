-- Prove2me | solution 1 for LocalSearchFL.CFL.summed_inequality_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:16:34.611664+00:00
-- url     : https://prove2.me/submissions/db550f26-a3b3-42e2-b201-0c762d48c831

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

set_option autoImplicit false

namespace LocalSearchFL.CFL.P2aa9c391

open LocalSearchFL.CFL

lemma cn_ne {m n : ℕ} (x : Fin m) (y : Fin n) : Fin.castAdd n x ≠ Fin.natAdd m y := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
  have := x.isLt
  omega

open Classical in
/-- The drop-add neighbour: drop the copies in `T`, add `l` copies of `s'`, reassign the
clients of `T` to the new copies in blocks of size `u s'`. -/
noncomputable def mkY {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ} (X : CFLSol Cl Fa u)
    (T : Finset (Fin X.n)) (s' : Fa) (l : ℕ) (hl : 1 ≤ l)
    (hcap : (X.nbhdSet T).card ≤ l * u s') (hu : 0 < u s') : CFLSol Cl Fa u where
  n := (Finset.univ \ T).toList.length + l
  loc := Fin.append
    (fun a : Fin (Finset.univ \ T).toList.length => X.loc (Finset.univ \ T).toList[(a : ℕ)])
    (fun _ : Fin l => s')
  σ := fun j => if h : X.σ j ∈ T then
      Fin.natAdd _ ⟨min ((X.nbhdSet T).toList.idxOf j / u s') (l - 1), by omega⟩
    else Fin.castAdd l ⟨(Finset.univ \ T).toList.idxOf (X.σ j),
      List.idxOf_lt_length_of_mem (by simp [h])⟩
  cap := by
    intro s
    induction s using Fin.addCases with
    | left a =>
      rw [Fin.append_left]
      refine le_trans (Finset.card_le_card ?_) (X.cap _)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      split_ifs at hj with h
      · exact absurd hj.symm (cn_ne _ _)
      · have h2 := (Fin.castAdd_inj).mp hj
        rw [← h2]
        simp [List.getElem_idxOf]
    | right b =>
      rw [Fin.append_right]
      calc _ ≤ (Finset.Ico (b.val * u s') (b.val * u s' + u s')).card := by
            apply Finset.card_le_card_of_injOn (fun j => (X.nbhdSet T).toList.idxOf j)
            · intro j hj
              simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
              split_ifs at hj with h
              · have hb := (Fin.natAdd_inj _).mp hj
                have hb' : min ((X.nbhdSet T).toList.idxOf j / u s') (l - 1) = b.val :=
                  congrArg Fin.val hb
                have hmem : j ∈ (X.nbhdSet T).toList := by simp [CFLSol.nbhdSet, h]
                have hlt : (X.nbhdSet T).toList.idxOf j < (X.nbhdSet T).card := by
                  simpa using List.idxOf_lt_length_of_mem hmem
                have hkd : (X.nbhdSet T).toList.idxOf j / u s' < l := by
                  rw [Nat.div_lt_iff_lt_mul hu]; omega
                have hbv : (X.nbhdSet T).toList.idxOf j / u s' = b.val := by omega
                have h1 := Nat.div_add_mod ((X.nbhdSet T).toList.idxOf j) (u s')
                have h2 := Nat.mod_lt ((X.nbhdSet T).toList.idxOf j) hu
                rw [hbv] at h1
                simp only [Finset.coe_Ico, Set.mem_Ico]
                rw [Nat.mul_comm] at h1
                constructor <;> omega
              · exact absurd hj (cn_ne _ _)
            · intro j₁ hj₁ j₂ hj₂ heq
              simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj₁
              split_ifs at hj₁ with h
              · have hmem : j₁ ∈ (X.nbhdSet T).toList := by
                  simp [CFLSol.nbhdSet, h]
                exact (List.idxOf_inj hmem).mp heq
              · exact absurd hj₁ (cn_ne _ _)
        _ = u s' := by simp

lemma fac_aux {Fa : Type} {m l : ℕ} (g : Fin m → Fa) (s' : Fa) :
    Multiset.map (Fin.append g (fun _ : Fin l => s')) (Finset.univ : Finset (Fin (m + l))).val =
      (↑(List.ofFn g) : Multiset Fa) + Multiset.replicate l s' := by
  rw [Fin.univ_val_map, List.ofFn_fin_append]
  simp only [List.ofFn_const]
  rw [← Multiset.coe_add, Multiset.coe_replicate]

lemma mkY_fac {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ} (X : CFLSol Cl Fa u)
    (T : Finset (Fin X.n)) (s' : Fa) (l : ℕ) (hl : 1 ≤ l)
    (hcap : (X.nbhdSet T).card ≤ l * u s') (hu : 0 < u s') :
    (mkY X T s' l hl hcap hu).facMultiset =
      Multiset.map X.loc (Finset.univ \ T).val + Multiset.replicate l s' := by
  have := fac_aux (l := l)
    (fun a : Fin (Finset.univ \ T).toList.length => X.loc (Finset.univ \ T).toList[(a : ℕ)]) s'
  rw [List.ofFn_getElem_eq_map, ← Multiset.map_coe, Finset.coe_toList] at this
  exact this

open Classical in
lemma mkY_locσ {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ} (X : CFLSol Cl Fa u)
    (T : Finset (Fin X.n)) (s' : Fa) (l : ℕ) (hl : 1 ≤ l)
    (hcap : (X.nbhdSet T).card ≤ l * u s') (hu : 0 < u s') (j : Cl) :
    (mkY X T s' l hl hcap hu).loc ((mkY X T s' l hl hcap hu).σ j) =
      if X.σ j ∈ T then s' else X.loc (X.σ j) := by
  simp only [mkY]
  split_ifs with h
  · rw [Fin.append_right]
  · rw [Fin.append_left]
    simp [List.getElem_idxOf]

lemma costF_eq_fac {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ} (f : Fa → ℝ) (Y : CFLSol Cl Fa u) :
    costF f Y = (Y.facMultiset.map f).sum := by
  unfold costF CFLSol.facMultiset
  rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

open Classical in
lemma fiber_sum {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ} (X : CFLSol Cl Fa u)
    (T : Finset (Fin X.n)) (h : Fin X.n → ℝ) :
    ∑ j, (if X.σ j ∈ T then h (X.σ j) else 0) = ∑ s ∈ T, ((X.nbhd s).card : ℝ) * h s := by
  rw [← Finset.sum_fiberwise Finset.univ X.σ]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => s ∈ T)]
  have h0 : ∑ s ∈ Finset.univ.filter (fun s => s ∉ T),
      ∑ j ∈ Finset.univ.filter (fun j => X.σ j = s), (if X.σ j ∈ T then h (X.σ j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs hj
    simp [hj, hs]
  rw [h0, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_congr rfl (g := fun _ => h s)]
  · simp [CFLSol.nbhd]
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [hj, hs]

open Classical in
lemma per_o {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (T : Finset (Fin X.n)) (s' : Fa)
    (hu : 0 < u s') :
    ∑ s ∈ T, f (X.loc s) ≤ f s' +
      ∑ s ∈ T, ((X.nbhd s).card : ℝ) * (I.cf (X.loc s) s' + f s' / (u s' : ℝ)) := by
  set N := (X.nbhdSet T).card with hN
  set U := u s' with hU
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hu
  set x : ℝ := (N : ℝ) / U with hx
  have hx0 : 0 ≤ x := by positivity
  set l := max 1 ⌈x⌉₊ with hl
  have hl1 : 1 ≤ l := le_max_left _ _
  have hcap : N ≤ l * U := by
    have h1 : (N : ℝ) ≤ (⌈x⌉₊ : ℝ) * U := by
      have := Nat.le_ceil x
      rw [hx, div_le_iff₀ hUpos] at this
      exact this
    have h2 : N ≤ ⌈x⌉₊ * U := by exact_mod_cast h1
    exact le_trans h2 (Nat.mul_le_mul_right _ (le_max_right _ _))
  have hlx : (l : ℝ) ≤ 1 + x := by
    rw [hl]
    rcases le_total 1 ⌈x⌉₊ with h | h
    · rw [max_eq_right h]
      have := Nat.ceil_lt_add_one hx0
      linarith
    · rw [max_eq_left h]; simp; linarith
  have hopt := hX (mkY X T s' l hl1 hcap hu)
    (Or.inr ⟨T, s', l, hl1, hcap, mkY_fac X T s' l hl1 hcap hu⟩)
  -- costs
  have hFX : costF f X = ∑ s ∈ Finset.univ \ T, f (X.loc s) + ∑ s ∈ T, f (X.loc s) := by
    rw [Finset.sum_sdiff (Finset.subset_univ T)]; rfl
  have hFY : costF f (mkY X T s' l hl1 hcap hu) =
      ∑ s ∈ Finset.univ \ T, f (X.loc s) + l * f s' := by
    rw [costF_eq_fac, mkY_fac]
    simp [Multiset.map_map, Finset.sum_eq_multiset_sum]
  have hSY : costS I (mkY X T s' l hl1 hcap hu) ≤ costS I X +
      ∑ j, (if X.σ j ∈ T then I.cf (X.loc (X.σ j)) s' else 0) := by
    unfold costS
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    rw [mkY_locσ]
    split_ifs with h
    · have := I.triangle (Sum.inl j) (Sum.inr (X.loc (X.σ j))) (Sum.inr s')
      simpa [MetricInstance.c, MetricInstance.cf] using this
    · simp
  rw [fiber_sum X T (fun s => I.cf (X.loc s) s')] at hSY
  have hNsum : (N : ℝ) = ∑ s ∈ T, ((X.nbhd s).card : ℝ) * 1 := by
    rw [← fiber_sum X T (fun _ => 1)]
    simp [hN, CFLSol.nbhdSet, Finset.sum_boole]
  have hlf : (l : ℝ) * f s' ≤ f s' + ∑ s ∈ T, ((X.nbhd s).card : ℝ) * (f s' / U) := by
    have : ∑ s ∈ T, ((X.nbhd s).card : ℝ) * (f s' / U) = x * f s' := by
      rw [hx, hNsum, Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro s _; ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hlx (hf s')
    linarith
  unfold cost at hopt
  rw [hFX, hFY] at hopt
  have hsplit : ∑ s ∈ T, ((X.nbhd s).card : ℝ) * (I.cf (X.loc s) s' + f s' / (u s' : ℝ)) =
      ∑ s ∈ T, ((X.nbhd s).card : ℝ) * I.cf (X.loc s) s' +
      ∑ s ∈ T, ((X.nbhd s).card : ℝ) * (f s' / U) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro s _; ring
  rw [hsplit]
  linarith

end LocalSearchFL.CFL.P2aa9c391

open LocalSearchFL.CFL in
theorem solution {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u)
    (τ : Fin X.n → Fin O.n) :
    ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o), f (X.loc s) ≤
      ∑ o, f (O.loc o) +
        ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o),
          ((X.nbhd s).card : ℝ) * (I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ∧
    ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o), f (X.loc s) = costF f X := by
  constructor
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro o _
    exact LocalSearchFL.CFL.P2aa9c391.per_o I u f hf X hX _ (O.loc o) (hu _)
  · rw [Finset.sum_fiberwise Finset.univ τ]
    rfl
