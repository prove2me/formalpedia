-- Prove2me | solution 1 for LocalSearchFL.CFL.cfl_locality_gap
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:16:45.501288+00:00
-- url     : https://prove2.me/submissions/b890743d-8250-48a2-a4bc-6c78568438e6

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt



namespace LocalSearchFL.CFL

theorem aux_da52_exists {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ}
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (X : CFLSol Cl Fa u)
    (T : Finset (Fin X.n)) (s' : Fa) (l : ℕ) (hl : 1 ≤ l)
    (hcap : (X.nbhdSet T).card ≤ l * u s') :
    ∃ Y : CFLSol Cl Fa u, IsDropAddNbr X Y ∧
      cost I f Y = ∑ s ∈ Finset.univ \ T, f (X.loc s) + (l : ℝ) * f s' +
        ∑ j, (if X.σ j ∈ T then I.c j s' else I.c j (X.loc (X.σ j))) := by
  classical
  set D : Finset (Fin X.n) := Finset.univ \ T with hD
  set k := D.card with hk
  let e : {x // x ∈ D} ≃ Fin k := D.equivFin
  set N := X.nbhdSet T with hN
  let G : {j // j ∈ N} ≃ Fin N.card := N.equivFin
  have hmem : ∀ j, X.σ j ∈ T → j ∈ N := by
    intro j h; simp [N, CFLSol.nbhdSet, h]
  have hmemD : ∀ s, s ∉ T → s ∈ D := by
    intro s h; simp [D, h]
  let p : ∀ j, X.σ j ∈ T → Fin l × Fin (u s') := fun j h =>
    finProdFinEquiv.symm (Fin.castLE hcap (G ⟨j, hmem j h⟩))
  let loc' : Fin (k + l) → Fa :=
    Fin.addCases (motive := fun _ => Fa) (fun i => X.loc (e.symm i).1) (fun _ => s')
  let σ' : Cl → Fin (k + l) := fun j =>
    if h : X.σ j ∈ T then Fin.natAdd k (p j h).1
    else Fin.castAdd l (e ⟨X.σ j, hmemD _ h⟩)
  have hloc : ∀ j, loc' (σ' j) = if X.σ j ∈ T then s' else X.loc (X.σ j) := by
    intro j
    by_cases h : X.σ j ∈ T
    · simp [σ', loc', h]
    · simp [σ', loc', h]
  have hcap' : ∀ s, (Finset.univ.filter (fun j => σ' j = s)).card ≤ u (loc' s) := by
    intro s
    induction s using Fin.addCases with
    | left i =>
      have hsub : Finset.univ.filter (fun j => σ' j = Fin.castAdd l i) ⊆
          Finset.univ.filter (fun j => X.σ j = (e.symm i).1) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        by_cases h : X.σ j ∈ T
        · simp only [σ', h, dif_pos] at hj
          exact absurd hj (by
            intro hh
            have := congrArg Fin.val hh
            simp at this
            omega)
        · simp only [σ', h, dif_neg, not_false_eq_true] at hj
          have h2 : e ⟨X.σ j, hmemD _ h⟩ = i := Fin.castAdd_injective _ _ hj
          have h3 : (⟨X.σ j, hmemD _ h⟩ : {x // x ∈ D}) = e.symm i := by
            rw [← h2]; simp
          exact congrArg Subtype.val h3
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ u (X.loc (e.symm i).1) := X.cap _
        _ = u (loc' (Fin.castAdd l i)) := by simp [loc']
    | right i =>
      have hl' : loc' (Fin.natAdd k i) = s' := by simp [loc']
      rw [hl']
      let g : Cl → ℕ := fun j => if h : X.σ j ∈ T then ((p j h).2 : ℕ) else 0
      have hmaps : ∀ j ∈ Finset.univ.filter (fun j => σ' j = Fin.natAdd k i),
          g j ∈ Finset.range (u s') := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        by_cases h : X.σ j ∈ T
        · simp [g, h]
        · simp only [σ', h, dif_neg, not_false_eq_true] at hj
          exfalso
          have := congrArg Fin.val hj
          simp at this
          omega
      have hinj : Set.InjOn g (Finset.univ.filter (fun j => σ' j = Fin.natAdd k i)) := by
        intro j₁ hj₁ j₂ hj₂ hg
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj₁ hj₂
        by_cases h₁ : X.σ j₁ ∈ T
        · by_cases h₂ : X.σ j₂ ∈ T
          · simp only [σ', h₁, h₂, dif_pos] at hj₁ hj₂
            have e1 : (p j₁ h₁).1 = i := Fin.natAdd_injective _ _ hj₁
            have e2 : (p j₂ h₂).1 = i := Fin.natAdd_injective _ _ hj₂
            simp only [g, h₁, h₂, dif_pos] at hg
            have e3 : (p j₁ h₁).2 = (p j₂ h₂).2 := Fin.ext hg
            have e4 : p j₁ h₁ = p j₂ h₂ := Prod.ext (e1.trans e2.symm) e3
            simp only [p] at e4
            have e5 := finProdFinEquiv.symm.injective e4
            have e6 := Fin.castLE_injective _ e5
            have e7 := G.injective e6
            exact congrArg Subtype.val e7
          · simp only [σ', h₂, dif_neg, not_false_eq_true] at hj₂
            exfalso
            have := congrArg Fin.val hj₂
            simp at this
            omega
        · simp only [σ', h₁, dif_neg, not_false_eq_true] at hj₁
          exfalso
          have := congrArg Fin.val hj₁
          simp at this
          omega
      calc _ ≤ (Finset.range (u s')).card := Finset.card_le_card_of_injOn g hmaps hinj
        _ = u s' := Finset.card_range _
  refine ⟨{ n := k + l, loc := loc', σ := σ', cap := hcap' }, ?_, ?_⟩
  · refine ⟨T, s', l, hl, hcap, ?_⟩
    simp only [CFLSol.facMultiset]
    rw [Fin.univ_val_map, List.ofFn_add, ← Multiset.coe_add]
    congr 1
    · rw [← Fin.univ_val_map]
      have hc : ∀ i : Fin k, loc' (Fin.castAdd l i) = (X.loc ∘ Subtype.val ∘ e.symm) i := by
        intro i; simp [loc']
      refine (Multiset.map_congr rfl (fun i _ => hc i)).trans ?_
      rw [← Multiset.map_map, ← Multiset.map_map, Multiset.map_univ_val_equiv,
        Finset.univ_eq_attach, Finset.attach_val, Multiset.attach_map_val]
    · have : (fun i : Fin l => loc' (Fin.natAdd k i)) = fun _ => s' := by
        funext i; simp [loc']
      rw [this]
      simp [Multiset.coe_replicate]
  · simp only [cost, costF, costS]
    rw [Fin.sum_univ_add]
    have h1 : ∑ i : Fin k, f (loc' (Fin.castAdd l i)) = ∑ s ∈ D, f (X.loc s) := by
      have : ∀ i : Fin k, f (loc' (Fin.castAdd l i)) = f (X.loc (e.symm i).1) := by
        intro i; simp [loc']
      rw [Finset.sum_congr rfl (fun i _ => this i)]
      rw [Equiv.sum_comp e.symm (fun x : {x // x ∈ D} => f (X.loc x.1))]
      exact Finset.sum_coe_sort D (fun s => f (X.loc s))
    have h2 : ∑ i : Fin l, f (loc' (Fin.natAdd k i)) = (l : ℝ) * f s' := by
      simp [loc']
    have h3 : ∑ j, I.c j (loc' (σ' j)) =
        ∑ j, (if X.σ j ∈ T then I.c j s' else I.c j (X.loc (X.σ j))) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hloc j]
      split_ifs <;> rfl
    rw [h1, h2, h3]

theorem aux_da52_nbhd_sum {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ} (X : CFLSol Cl Fa u)
    (U : Finset (Fin X.n)) (w : Fin X.n → ℝ) :
    ∑ s ∈ U, ((X.nbhd s).card : ℝ) * w s = ∑ j, (if X.σ j ∈ U then w (X.σ j) else 0) := by
  classical
  have h : ∀ s, ((X.nbhd s).card : ℝ) * w s = ∑ j, (if X.σ j = s then w s else 0) := by
    intro s
    rw [← Finset.sum_filter]
    simp [CFLSol.nbhd, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun s _ => h s), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_ite_eq]


theorem da52_core {Cl Fa : Type} [Fintype Cl] [Nonempty Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (U : Finset (Fin X.n)) (s' : Fa) :
    ∑ s ∈ U, f (X.loc s) ≤
      (⌈((X.nbhdSet U).card : ℝ) / (u s' : ℝ)⌉₊ : ℝ) * f s' +
        ∑ s ∈ U, ((X.nbhd s).card : ℝ) * I.cf (X.loc s) s' := by
  classical
  by_cases hN : (X.nbhdSet U).card = 0
  · have hNe : X.nbhdSet U = ∅ := Finset.card_eq_zero.mp hN
    have hnot : ∀ j, X.σ j ∉ U := by
      intro j hj
      have : j ∈ X.nbhdSet U := by simp [CFLSol.nbhdSet, hj]
      rw [hNe] at this; simp at this
    have hzero : ∀ s ∈ U, (X.nbhd s).card = 0 := by
      intro s hs
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro j hj
      simp [CFLSol.nbhd] at hj
      exact hnot j (hj ▸ hs)
    have hR : (⌈((X.nbhdSet U).card : ℝ) / (u s' : ℝ)⌉₊ : ℝ) * f s' +
        ∑ s ∈ U, ((X.nbhd s).card : ℝ) * I.cf (X.loc s) s' = 0 := by
      rw [hN]
      simp only [Nat.cast_zero, zero_div, Nat.ceil_zero, zero_mul, zero_add]
      refine Finset.sum_eq_zero (fun s hs => ?_)
      rw [hzero s hs]; simp
    rw [hR]
    obtain ⟨j0⟩ := ‹Nonempty Cl›
    set t := X.σ j0 with ht_def
    have ht : t ∉ U := hnot j0
    have hcapT : (X.nbhdSet (insert t U)).card ≤ 1 * u (X.loc t) := by
      rw [one_mul]
      refine le_trans (Finset.card_le_card ?_) (X.cap t)
      intro j hj
      simp only [CFLSol.nbhdSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert] at hj ⊢
      rcases hj with h | h
      · exact h
      · exact absurd h (hnot j)
    obtain ⟨Y, hY, hcost⟩ := aux_da52_exists I f X (insert t U) (X.loc t) 1 le_rfl hcapT
    have hle := hX Y (Or.inr hY)
    rw [hcost] at hle
    have hS : ∑ j, (if X.σ j ∈ insert t U then I.c j (X.loc t) else I.c j (X.loc (X.σ j)))
        = costS I X := by
      unfold costS
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs with h
      · rw [Finset.mem_insert] at h
        rcases h with h | h
        · rw [h]
        · exact absurd h (hnot j)
      · rfl
    rw [hS] at hle
    unfold cost costF at hle
    have hsplit := Finset.sum_sdiff (Finset.subset_univ (insert t U)) (f := fun s => f (X.loc s))
    rw [Finset.sum_insert ht] at hsplit
    push_cast at hle
    linarith
  · have hpos : 0 < (X.nbhdSet U).card := Nat.pos_of_ne_zero hN
    have hus : (0:ℝ) < u s' := by exact_mod_cast hu s'
    have hl1 : 1 ≤ ⌈((X.nbhdSet U).card : ℝ) / (u s' : ℝ)⌉₊ := by
      rw [Nat.one_le_ceil_iff]
      have : (0:ℝ) < (X.nbhdSet U).card := by exact_mod_cast hpos
      positivity
    have hcapU : (X.nbhdSet U).card ≤ ⌈((X.nbhdSet U).card : ℝ) / (u s' : ℝ)⌉₊ * u s' := by
      have h1 : ((X.nbhdSet U).card : ℝ) / (u s') ≤ ⌈((X.nbhdSet U).card : ℝ) / (u s' : ℝ)⌉₊ :=
        Nat.le_ceil _
      rw [div_le_iff₀ hus] at h1
      exact_mod_cast h1
    obtain ⟨Y, hY, hcost⟩ := aux_da52_exists I f X U s' _ hl1 hcapU
    have hle := hX Y (Or.inr hY)
    rw [hcost] at hle
    unfold cost costF costS at hle
    have hsplit := Finset.sum_sdiff (Finset.subset_univ U) (f := fun s => f (X.loc s))
    have htri : ∑ j, (if X.σ j ∈ U then I.c j s' else I.c j (X.loc (X.σ j))) ≤
        ∑ j, I.c j (X.loc (X.σ j)) +
          ∑ j, (if X.σ j ∈ U then I.cf (X.loc (X.σ j)) s' else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun j _ => ?_)
      split_ifs
      · exact I.triangle _ (Sum.inr (X.loc (X.σ j))) _
      · simp
    rw [aux_da52_nbhd_sum X U (fun s => I.cf (X.loc s) s')]
    linarith

theorem aux_spfb10_cf_le {Cl Fa : Type} (I : MetricInstance Cl Fa) (j : Cl) (a b : Fa) :
    I.cf a b ≤ I.c j a + I.c j b := by
  unfold MetricInstance.cf MetricInstance.c
  have h := I.triangle (Sum.inr a) (Sum.inl j) (Sum.inr b)
  rw [I.symm (Sum.inr a) (Sum.inl j)] at h
  exact h

theorem spfb10_core {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X O : CFLSol Cl Fa u) (hO : 0 < O.n) :
    ∃ τ : Fin X.n → Fin O.n,
      (∀ s o, I.cf (X.loc s) (O.loc (τ s)) + f (O.loc (τ s)) / (u (O.loc (τ s)) : ℝ) ≤
        I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ∧
      ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o),
          ((X.nbhd s).card : ℝ) * (I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ≤
        costS I X + costS I O + costF f O := by
  classical
  have : Nonempty (Fin O.n) := ⟨⟨0, hO⟩⟩
  set g : Fin X.n → Fin O.n → ℝ :=
    fun s o => I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ) with hg
  have hex : ∀ s, ∃ o, ∀ o', g s o ≤ g s o' := fun s => by
    obtain ⟨o, -, ho⟩ := Finset.exists_min_image Finset.univ (g s) Finset.univ_nonempty
    exact ⟨o, fun o' => ho o' (Finset.mem_univ _)⟩
  choose τ hτ using hex
  refine ⟨τ, hτ, ?_⟩
  change ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o), ((X.nbhd s).card : ℝ) * g s o ≤ _
  have h1 : ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o), ((X.nbhd s).card : ℝ) * g s o
      = ∑ s, ((X.nbhd s).card : ℝ) * g s (τ s) := by
    rw [← Finset.sum_fiberwise Finset.univ τ (fun s => ((X.nbhd s).card : ℝ) * g s (τ s))]
    apply Finset.sum_congr rfl
    intro o _
    apply Finset.sum_congr rfl
    intro s hs
    rw [(Finset.mem_filter.1 hs).2]
  have h2 : ∑ s, ((X.nbhd s).card : ℝ) * g s (τ s) = ∑ j, g (X.σ j) (τ (X.σ j)) := by
    rw [← Finset.sum_fiberwise Finset.univ X.σ (fun j => g (X.σ j) (τ (X.σ j)))]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_congr rfl (g := fun _ => g s (τ s))]
    · simp [CFLSol.nbhd, Finset.sum_const, nsmul_eq_mul]
    · intro j hj
      rw [(Finset.mem_filter.1 hj).2]
  have h3 : ∀ j, g (X.σ j) (τ (X.σ j)) ≤ I.c j (X.loc (X.σ j)) + I.c j (O.loc (O.σ j)) +
      f (O.loc (O.σ j)) / (u (O.loc (O.σ j)) : ℝ) := by
    intro j
    refine le_trans (hτ (X.σ j) (O.σ j)) ?_
    simp only [hg]
    have := aux_spfb10_cf_le I j (X.loc (X.σ j)) (O.loc (O.σ j))
    linarith
  have h4 : ∑ j, f (O.loc (O.σ j)) / (u (O.loc (O.σ j)) : ℝ) ≤ costF f O := by
    unfold costF
    rw [← Finset.sum_fiberwise Finset.univ O.σ
      (fun j => f (O.loc (O.σ j)) / (u (O.loc (O.σ j)) : ℝ))]
    apply Finset.sum_le_sum
    intro o _
    rw [Finset.sum_congr rfl (g := fun _ => f (O.loc o) / (u (O.loc o) : ℝ))]
    · rw [Finset.sum_const, nsmul_eq_mul]
      have hcap := O.cap o
      have hupos : (0 : ℝ) < (u (O.loc o) : ℝ) := by exact_mod_cast hu (O.loc o)
      have hcap' : ((Finset.univ.filter (fun j => O.σ j = o)).card : ℝ) ≤ (u (O.loc o) : ℝ) := by
        exact_mod_cast hcap
      have hdiv : 0 ≤ f (O.loc o) / (u (O.loc o) : ℝ) := div_nonneg (hf _) hupos.le
      calc ((Finset.univ.filter (fun j => O.σ j = o)).card : ℝ) * (f (O.loc o) / (u (O.loc o) : ℝ))
          ≤ (u (O.loc o) : ℝ) * (f (O.loc o) / (u (O.loc o) : ℝ)) :=
            mul_le_mul_of_nonneg_right hcap' hdiv
        _ = f (O.loc o) := by field_simp
    · intro j hj
      rw [(Finset.mem_filter.1 hj).2]
  rw [h1, h2]
  calc ∑ j, g (X.σ j) (τ (X.σ j))
      ≤ ∑ j, (I.c j (X.loc (X.σ j)) + I.c j (O.loc (O.σ j)) +
          f (O.loc (O.σ j)) / (u (O.loc (O.σ j)) : ℝ)) := Finset.sum_le_sum (fun j _ => h3 j)
    _ = costS I X + costS I O + ∑ j, f (O.loc (O.σ j)) / (u (O.loc (O.σ j)) : ℝ) := by
      unfold costS
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ costS I X + costS I O + costF f O := by linarith

theorem aux_add_exists {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] {u : Fa → ℕ}
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (X : CFLSol Cl Fa u)
    (a : Fa) (P : Finset Cl) (hP : P.card ≤ u a) :
    ∃ Y : CFLSol Cl Fa u, IsAddNbr X Y ∧
      cost I f Y = costF f X + f a +
        ∑ j, (if j ∈ P then I.c j a else I.c j (X.loc (X.σ j))) := by
  classical
  let loc' : Fin (X.n + 1) → Fa := Fin.snoc (α := fun _ => Fa) X.loc a
  let σ' : Cl → Fin (X.n + 1) := fun j => if j ∈ P then Fin.last _ else (X.σ j).castSucc
  have hcap' : ∀ s, (Finset.univ.filter (fun j => σ' j = s)).card ≤ u (loc' s) := by
    intro s
    induction s using Fin.lastCases with
    | last =>
      have hsub : Finset.univ.filter (fun j => σ' j = Fin.last _) ⊆ P := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, σ'] at hj
        by_contra h
        rw [if_neg h] at hj
        exact absurd hj (Fin.castSucc_ne_last _)
      have : loc' (Fin.last _) = a := by simp [loc']
      rw [this]
      exact (Finset.card_le_card hsub).trans hP
    | cast i =>
      have hsub : Finset.univ.filter (fun j => σ' j = i.castSucc) ⊆
          Finset.univ.filter (fun j => X.σ j = i) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, σ'] at hj ⊢
        by_cases h : j ∈ P
        · rw [if_pos h] at hj; exact absurd hj.symm (Fin.castSucc_ne_last _)
        · rw [if_neg h] at hj; exact Fin.castSucc_injective _ hj
      have : loc' i.castSucc = X.loc i := by simp [loc']
      rw [this]
      exact (Finset.card_le_card hsub).trans (X.cap i)
  refine ⟨{ n := X.n + 1, loc := loc', σ := σ', cap := hcap' }, ⟨a, ?_⟩, ?_⟩
  · simp only [CFLSol.facMultiset]
    rw [Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ']
    simp only [loc', List.concat_eq_append, Fin.snoc_castSucc, Fin.snoc_last]
    rw [← Multiset.coe_add]; rfl
  · simp only [cost, costF, costS]
    rw [Fin.sum_univ_castSucc]
    have h1 : ∑ i : Fin X.n, f (loc' i.castSucc) = ∑ i, f (X.loc i) := by simp [loc']
    have h2 : loc' (Fin.last _) = a := by simp [loc']
    have h3 : ∑ j, I.c j (loc' (σ' j)) =
        ∑ j, (if j ∈ P then I.c j a else I.c j (X.loc (X.σ j))) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h : j ∈ P
      · simp [σ', h, loc']
      · simp [σ', h, loc']
    rw [h1, h2, h3]

theorem service_core {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ}
    (I : MetricInstance Cl Fa) (f : Fa → ℝ)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    costS I X ≤ costF f O + costS I O := by
  classical
  have key : ∀ o : Fin O.n, 0 ≤ f (O.loc o) +
      ∑ j, (if O.σ j = o then I.c j (O.loc o) - I.c j (X.loc (X.σ j)) else 0) := by
    intro o
    obtain ⟨Y, hY, hc⟩ := aux_add_exists I f X (O.loc o) (Finset.univ.filter (fun j => O.σ j = o))
      (O.cap o)
    have hle := hX Y (Or.inl hY)
    rw [hc] at hle
    unfold cost costS at hle
    have : ∑ j, (if j ∈ Finset.univ.filter (fun j => O.σ j = o) then I.c j (O.loc o)
        else I.c j (X.loc (X.σ j))) = ∑ j, I.c j (X.loc (X.σ j)) +
        ∑ j, (if O.σ j = o then I.c j (O.loc o) - I.c j (X.loc (X.σ j)) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h : O.σ j = o <;> simp [h]
    linarith
  have hs := Finset.sum_nonneg (fun o (_ : o ∈ Finset.univ) => key o)
  rw [Finset.sum_add_distrib, Finset.sum_comm] at hs
  have : ∀ j : Cl, ∑ o : Fin O.n, (if O.σ j = o then I.c j (O.loc o) - I.c j (X.loc (X.σ j))
      else 0) = I.c j (O.loc (O.σ j)) - I.c j (X.loc (X.σ j)) := by
    intro j; rw [Finset.sum_ite_eq]; simp
  simp only [this, Finset.sum_sub_distrib] at hs
  unfold costF costS
  linarith

theorem facility_core {Cl Fa : Type} [Fintype Cl] [Nonempty Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    costF f X ≤ 3 * costF f O + 2 * costS I O := by
  classical
  have hO : 0 < O.n := by
    obtain ⟨j⟩ := ‹Nonempty Cl›
    exact Nat.pos_of_ne_zero (fun h => (h ▸ O.σ j).elim0)
  obtain ⟨τ, -, hτ⟩ := spfb10_core I u hu f hf X O hO
  set g : Fin X.n → Fin O.n → ℝ :=
    fun s o => I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ) with hg
  have hloc : ∀ o : Fin O.n, ∑ s ∈ Finset.univ.filter (fun s => τ s = o), f (X.loc s) ≤
      f (O.loc o) + ∑ s ∈ Finset.univ.filter (fun s => τ s = o),
        ((X.nbhd s).card : ℝ) * g s o := by
    intro o
    set U := Finset.univ.filter (fun s => τ s = o) with hU
    have h1 := da52_core I u hu f hf X hX U (O.loc o)
    have hcard : ((X.nbhdSet U).card : ℝ) = ∑ s ∈ U, ((X.nbhd s).card : ℝ) := by
      have := aux_da52_nbhd_sum X U (fun _ => (1:ℝ))
      simp only [mul_one] at this
      rw [this]
      simp [CFLSol.nbhdSet, Finset.sum_boole]
    have hupos : (0:ℝ) < u (O.loc o) := by exact_mod_cast hu _
    have hceil : (⌈((X.nbhdSet U).card : ℝ) / (u (O.loc o) : ℝ)⌉₊ : ℝ) ≤
        ((X.nbhdSet U).card : ℝ) / (u (O.loc o) : ℝ) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have h2 : (⌈((X.nbhdSet U).card : ℝ) / (u (O.loc o) : ℝ)⌉₊ : ℝ) * f (O.loc o) ≤
        (((X.nbhdSet U).card : ℝ) / (u (O.loc o) : ℝ) + 1) * f (O.loc o) :=
      mul_le_mul_of_nonneg_right hceil (hf _)
    have h3 : ∑ s ∈ U, ((X.nbhd s).card : ℝ) * g s o =
        ((X.nbhdSet U).card : ℝ) / (u (O.loc o) : ℝ) * f (O.loc o) +
        ∑ s ∈ U, ((X.nbhd s).card : ℝ) * I.cf (X.loc s) (O.loc o) := by
      rw [hcard, Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp only [hg]; ring
    linarith
  have hsum := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) => hloc o)
  rw [Finset.sum_add_distrib] at hsum
  have hF : ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o), f (X.loc s) = costF f X := by
    unfold costF
    exact Finset.sum_fiberwise Finset.univ τ (fun s => f (X.loc s))
  rw [hF] at hsum
  have hS := service_core I f X hX O
  change costF f X ≤ costF f O + _ at hsum
  have hτ' : ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o),
      ((X.nbhd s).card : ℝ) * g s o ≤ costS I X + costS I O + costF f O := hτ
  linarith

theorem gap_core {Cl Fa : Type} [Fintype Cl] [Nonempty Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    cost I f X ≤ 4 * cost I f O := by
  have h1 := facility_core I u hu f hf X hX O
  have h2 := service_core I f X hX O
  have h3 : 0 ≤ costS I O := Finset.sum_nonneg (fun j _ => I.nonneg _ _)
  unfold cost
  linarith

end LocalSearchFL.CFL

open LocalSearchFL.CFL


theorem solution {Cl Fa : Type} [Fintype Cl] [Nonempty Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    cost I f X ≤ 4 * cost I f O := by
  exact gap_core I u hu f hf X hX O
