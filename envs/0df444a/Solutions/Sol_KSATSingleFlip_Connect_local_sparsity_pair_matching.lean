-- Prove2me | solution 1 for KSATSingleFlip.Connect.local_sparsity_pair_matching
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:43:05.606666+00:00
-- url     : https://prove2.me/submissions/b436f667-5ef2-4dda-bf79-21d36cada0f1

import Definitions.Def_KSATSingleFlip_Connect_Repair

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- Hall's condition for pairs of variables per clause gives a pair matching. -/
theorem audit_pair_matching_of_hall {n : ℕ} (Φ : GFormula (Fin n))
    (J : Finset (Fin Φ.length))
    (hHall : ∀ K ⊆ J, 2 * K.card ≤ (K.biUnion (fun c => vbl (Φ.get c))).card) :
    ∃ M : Fin Φ.length → Finset (Fin n), IsPairMatching Φ J M := by
  classical
  let I := ↥J × Fin 2
  let scopes : I → Finset (Fin n) := fun p => vbl (Φ.get p.1.1)
  have hHall' : ∀ H : Finset I, H.card ≤ (H.biUnion scopes).card := by
    intro H
    let K : Finset (Fin Φ.length) := H.image (fun p => p.1.1)
    have hKJ : K ⊆ J := by
      intro c hc
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hc
      exact p.1.2
    let f : I → Fin Φ.length × Fin 2 := fun p => (p.1.1, p.2)
    have hf : Function.Injective f := by
      intro a b hab
      have hfst : a.1 = b.1 := Subtype.ext (Prod.mk.inj hab).1
      have hsnd : a.2 = b.2 := (Prod.mk.inj hab).2
      exact Prod.ext hfst hsnd
    have himage : H.image f ⊆ K.product Finset.univ := by
      intro p hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, Finset.mem_univ _⟩
    have hcard : H.card ≤ 2 * K.card := by
      have h := Finset.card_le_card himage
      rw [Finset.card_image_of_injective H hf] at h
      simpa [Finset.product_eq_sprod, Finset.card_product, Nat.mul_comm] using h
    have hunion : H.biUnion scopes = K.biUnion (fun c => vbl (Φ.get c)) := by
      ext v
      simp only [Finset.mem_biUnion, K, Finset.mem_image, scopes]
      constructor
      · rintro ⟨p, hp, hv⟩
        exact ⟨p.1.1, ⟨p, hp, rfl⟩, hv⟩
      · rintro ⟨c, ⟨p, hp, rfl⟩, hv⟩
        exact ⟨p, hp, hv⟩
    rw [hunion]
    exact le_trans hcard (hHall K hKJ)
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' scopes).mp hHall'
  let M : Fin Φ.length → Finset (Fin n) := fun c =>
    if hc : c ∈ J then Finset.univ.image (fun i : Fin 2 => f (⟨c, hc⟩, i)) else ∅
  refine ⟨M, ?_⟩
  constructor
  · intro c hc
    have hM : M c = Finset.univ.image (fun i : Fin 2 => f (⟨c, hc⟩, i)) := by simp [M, hc]
    rw [hM]
    constructor
    · intro v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact hf (⟨c, hc⟩, i)
    · rw [Finset.card_image_of_injective]
      · simp
      · intro i j hij
        have he := hfinj hij
        exact congrArg Prod.snd he
  · intro c hc d hd hne
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    have hM : M c = Finset.univ.image (fun i : Fin 2 => f (⟨c, hc⟩, i)) := by simp [M, hc]
    have hM' : M d = Finset.univ.image (fun i : Fin 2 => f (⟨d, hd⟩, i)) := by simp [M, hd]
    rw [hM] at hv
    rw [hM'] at hv'
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv'
    have he := hfinj (hi.trans hj.symm)
    exact hne (congrArg (fun p : I => p.1.1) he)

/-- Local sparsity gives the pair-matching Hall condition for a small collection
of nonempty-scope clauses, as used in Lemma 7.12. -/
theorem audit_local_sparsity_pair_matching {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (hk : 4 ≤ k) (hscope : ∀ c : Fin Φ.length, (vbl (Φ.get c)).Nonempty)
    (hLS : LS k Φ) (J : Finset (Fin Φ.length))
    (hsmall : (2 * J.card : ℝ) ≤ rho k * n) :
    ∃ M : Fin Φ.length → Finset (Fin n), IsPairMatching Φ J M := by
  classical
  apply audit_pair_matching_of_hall Φ J
  intro K hKJ
  let A := K.biUnion (fun c => vbl (Φ.get c))
  by_contra hbad
  have hlt : A.card < 2 * K.card := Nat.lt_of_not_ge hbad
  have hKnon : K.Nonempty := by
    by_contra hzero
    have : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hzero
    subst K
    simp [A] at hlt
  obtain ⟨c, hc⟩ := hKnon
  obtain ⟨v, hv⟩ := hscope c
  have hApos : 0 < A.card := Finset.card_pos.mpr
    ⟨v, Finset.mem_biUnion.mpr ⟨c, hc, hv⟩⟩
  have hKcard : K.card ≤ J.card := Finset.card_le_card hKJ
  have hAsmall : (A.card : ℝ) ≤ rho k * n := by
    have hreal : (A.card : ℝ) < 2 * K.card := by exact_mod_cast hlt
    have hKreal : (K.card : ℝ) ≤ J.card := by exact_mod_cast hKcard
    linarith
  let Cset : Finset (Fin Φ.length) := Finset.univ.filter fun c => vbl (Φ.get c) ⊆ A
  have hKC : K ⊆ Cset := by
    intro d hd
    change d ∈ Finset.univ.filter _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro u hu
    exact Finset.mem_biUnion.mpr ⟨d, hd, hu⟩
  have hcount : (K.card : ℝ) ≤ Cset.card := by exact_mod_cast Finset.card_le_card hKC
  have hLS' : (Cset.card : ℝ) < 2 * A.card / k := hLS A hApos hAsmall
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLSmul : (Cset.card : ℝ) * k < 2 * A.card := (lt_div_iff₀ hkpos).mp hLS'
  have hkmul : (K.card : ℝ) * k ≤ (Cset.card : ℝ) * k :=
    mul_le_mul_of_nonneg_right hcount hkpos.le
  have hfour : 4 * (K.card : ℝ) ≤ (K.card : ℝ) * k := by
    have hkreal : (4 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hAless : (A.card : ℝ) < 2 * K.card := by exact_mod_cast hlt
  linarith

/-- Under the local-sparsity size condition, a Repair step cannot return Fail. -/
theorem audit_no_fail_of_small_matching {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (s : RState Φ x)
    (c : Fin Φ.length) (hk : 4 ≤ k)
    (hscope : ∀ c : Fin Φ.length, (vbl (Φ.get c)).Nonempty) (hLS : LS k Φ)
    (hsmall : (2 * (insert c s.J).card : ℝ) ≤ rho k * n) :
    ¬ RStep k Φ I0 x s c none := by
  intro hstep
  obtain ⟨_, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, _, _, heq⟩ := htree
    contradiction
  · obtain ⟨_, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', _, _, heq⟩ := hsuccess
      contradiction
    · obtain ⟨hnone, _⟩ := hfail
      exact hnone (audit_local_sparsity_pair_matching k Φ hk hscope hLS (insert c s.J) hsmall)

/-- Proper positive-width clauses have nonempty scopes. -/
theorem audit_proper_scopes_nonempty {n k : ℕ}
    (Φp : List (OAI.FixedClauseThreshold.ProperClause n k)) (hk : 0 < k) :
    ∀ c : Fin (ofList Φp).length, (vbl ((ofList Φp).get c)).Nonempty := by
  intro c
  have hc : (ofList Φp).get c ∈ ofList Φp := List.get_mem _ _
  unfold ofList at hc
  obtain ⟨C, _, hC⟩ := List.mem_map.mp hc
  have hcard : (vbl C.1).card = k := C.2
  have hnon : (vbl C.1).Nonempty := Finset.card_pos.mp (by omega)
  rw [hC] at hnon
  exact hnon

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

/-- Local sparsity yields a pair matching for every sufficiently small clause family. -/
theorem solution {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (hk : 4 ≤ k) (hscope : ∀ c : Fin Φ.length, (vbl (Φ.get c)).Nonempty)
    (hLS : LS k Φ) (J : Finset (Fin Φ.length))
    (hsmall : (2 * J.card : ℝ) ≤ rho k * n) :
    ∃ M : Fin Φ.length → Finset (Fin n), IsPairMatching Φ J M :=
  audit_local_sparsity_pair_matching k Φ hk hscope hLS J hsmall
