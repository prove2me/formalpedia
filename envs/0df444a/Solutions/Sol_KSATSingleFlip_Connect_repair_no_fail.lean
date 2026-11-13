-- Prove2me | solution 1 for KSATSingleFlip.Connect.repair_no_fail
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:51:41.729423+00:00
-- url     : https://prove2.me/submissions/6bc4e00b-a659-42e0-85df-223f834a69c2

import Definitions.Def_KSATSingleFlip_Connect_Repair

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

private def audit_matching_assigned_covered {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) : Prop :=
  ∀ c ∈ s.J, satSet x (Φ.get c) ⊆ s.U

/-- All x-true literals of matching-assigned clauses lie in U. -/
theorem audit_step_preserves_matching_assigned_covered {n : ℕ} (k : ℕ)
    (Φ : GFormula (Fin n)) (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (s s' : RState Φ x) (c : Fin Φ.length)
    (hstep : RStep k Φ I0 x s c (some s'))
    (hcover : audit_matching_assigned_covered Φ x s) :
    audit_matching_assigned_covered Φ x s' := by
  obtain ⟨hpend, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, _, _, heq⟩ := htree
    cases heq
    intro d hd v hv
    exact Finset.mem_union_left _ (hcover d hd hv)
  · obtain ⟨_, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', _, _, heq⟩ := hsuccess
      cases heq
      intro d hd v hv
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact Finset.mem_union_left _ (hpend.2 hv)
      · exact Finset.mem_union_left _ (hcover d hd hv)
    · obtain ⟨_, heq⟩ := hfail
      contradiction

theorem audit_reach_matching_assigned_covered {n : ℕ} (k : ℕ)
    (Φ : GFormula (Fin n)) (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (W : Finset (Fin n)) (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    audit_matching_assigned_covered Φ x s := by
  have hgen : ∀ s t : RState Φ x, ∀ j, RepairReach k Φ I0 x s t j →
      audit_matching_assigned_covered Φ x s → audit_matching_assigned_covered Φ x t := by
    intro s t j hreach
    induction hreach with
    | refl s => intro hs; exact hs
    | step s s' t c j hstep hreach ih =>
      intro hs
      exact ih (audit_step_preserves_matching_assigned_covered k Φ I0 x s s' c hstep hs)
  apply hgen _ _ _ h
  simp [audit_matching_assigned_covered, RState.init]

/-- Matching clauses retain the certificate that no small tree avoiding the
current U can be rooted in their scope. -/
def audit_no_tree_certificate {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (s : RState Φ x) : Prop :=
  ∀ c ∈ s.J, ¬ ∃ T : ForcingTree Φ x, IsSmallTree k Φ I0 x T ∧
    T.root ∈ vbl (Φ.get c) ∧ Disjoint T.vars s.U

private theorem disjoint_mono_U {n : ℕ} (T U U' : Finset (Fin n))
    (hUU : U ⊆ U') (hdisj : Disjoint T U') : Disjoint T U :=
  hdisj.mono_right hUU

/-- The no-available-tree certificate is preserved by each successful step. -/
theorem audit_step_no_tree_certificate {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (s s' : RState Φ x) (c : Fin Φ.length)
    (hstep : RStep k Φ I0 x s c (some s'))
    (hcert : audit_no_tree_certificate k Φ I0 x s) :
    audit_no_tree_certificate k Φ I0 x s' := by
  obtain ⟨_, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, _, _, heq⟩ := htree
    cases heq
    intro d hd ⟨T', hsmall, hroot, hdisj⟩
    exact hcert d hd ⟨T', hsmall, hroot, disjoint_mono_U _ _ _ Finset.subset_union_left hdisj⟩
  · obtain ⟨hnotree, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', _, _, heq⟩ := hsuccess
      cases heq
      intro d hd ⟨T', hsmall, hroot, hdisj⟩
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact hnotree ⟨T', hsmall, hroot, disjoint_mono_U _ _ _ Finset.subset_union_left hdisj⟩
      · exact hcert d hd ⟨T', hsmall, hroot, disjoint_mono_U _ _ _ Finset.subset_union_left hdisj⟩
    · obtain ⟨_, heq⟩ := hfail
      contradiction

/-- Every state reachable from the initial state carries the no-tree certificate. -/
theorem audit_reach_no_tree_certificate {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    audit_no_tree_certificate k Φ I0 x s := by
  have hgen : ∀ s t : RState Φ x, ∀ j, RepairReach k Φ I0 x s t j →
      audit_no_tree_certificate k Φ I0 x s → audit_no_tree_certificate k Φ I0 x t := by
    intro s t j hreach
    induction hreach with
    | refl s => intro hs; exact hs
    | step s s' t c j hstep hreach ih =>
      intro hs
      exact ih (audit_step_no_tree_certificate k Φ I0 x s s' c hstep hs)
  apply hgen _ _ _ h
  simp [audit_no_tree_certificate, RState.init]

private theorem get_mem_subF {n : ℕ} (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (c : Fin Φ.length) (hc : c ∈ I0) :
    Φ.get c ∈ subF Φ I0 := by
  unfold subF
  apply List.mem_filterMap.mpr
  exact ⟨c, List.mem_finRange _, by simp [hc]⟩

/-- Under x-satisfiability of Φ₀, every clause outside omittedWeak is
one-true in Φ₀ or multi-true in Φ⁺. -/
theorem audit_not_weak_classification {n : ℕ} (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (hx : x ∈ sols (subF Φ I0)) (c : Fin Φ.length)
    (hnot : c ∉ omittedWeak Φ I0 x) : c ∈ Cforce Φ I0 x ∨ c ∈ Cmulti Φ x := by
  have hsat : FSat x (subF Φ I0) := by simpa [sols] using hx
  by_cases hc : c ∈ I0
  · have hcsat : ClauseSat x (Φ.get c) := hsat _ (get_mem_subF Φ I0 c hc)
    obtain ⟨v, hv⟩ := hcsat
    have hpos : 0 < (satSet x (Φ.get c)).card := by
      apply Finset.card_pos.mpr
      refine ⟨v, ?_⟩
      unfold satSet
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hv⟩
    by_cases hmulti : 2 ≤ (satSet x (Φ.get c)).card
    · right
      unfold Cmulti
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hmulti⟩
    · left
      unfold Cforce
      rw [Finset.mem_filter]
      refine ⟨hc, ?_⟩
      omega
  · right
    unfold Cmulti
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hsmall
    have hw : c ∈ omittedWeak Φ I0 x := by
      unfold omittedWeak
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc⟩, ?_⟩
      omega
    exact hnot hw

/-- Every matching clause outside omittedWeak is counted by NoTree(U), provided
matching clauses' x-true literals lie in U. -/
theorem audit_matching_nonweak_counted {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (s : RState Φ x)
    (hx : x ∈ sols (subF Φ I0)) (hcert : audit_no_tree_certificate k Φ I0 x s)
    (hcover : ∀ c ∈ s.J, satSet x (Φ.get c) ⊆ s.U)
    (c : Fin Φ.length) (hc : c ∈ s.J) (hnot : c ∉ omittedWeak Φ I0 x) :
    c ∈ ((Cforce Φ I0 x ∪ Cmulti Φ x).filter fun d =>
      satSet x (Φ.get d) ⊆ s.U ∧
        ¬ ∃ u, FalseLitOn x (Φ.get d) u ∧ HasSmallCFT Φ I0 x u (Real.log k ^ 6) s.U) := by
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_union.mpr (audit_not_weak_classification Φ I0 x hx c hnot), hcover c hc, ?_⟩
  rintro ⟨u, hfalse, T, hroot, hcomplete, hsize, hdisj⟩
  have hrootScope : T.root ∈ vbl (Φ.get c) := by
    rw [hroot]
    unfold vbl
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold FalseLitOn at hfalse
    rw [hfalse]
    simp
  exact hcert c hc ⟨T, ⟨hcomplete, hsize⟩, hrootScope, hdisj⟩

/-- The number of matching clauses is at most omittedWeak plus NoTree(U). -/
theorem audit_matching_card_le_weak_add_notree {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (s : RState Φ x)
    (hx : x ∈ sols (subF Φ I0)) (hcert : audit_no_tree_certificate k Φ I0 x s)
    (hcover : ∀ c ∈ s.J, satSet x (Φ.get c) ⊆ s.U) :
    s.J.card ≤ (omittedWeak Φ I0 x).card + NoTree k Φ I0 x s.U := by
  let D := omittedWeak Φ I0 x
  let N := (Cforce Φ I0 x ∪ Cmulti Φ x).filter fun d =>
      satSet x (Φ.get d) ⊆ s.U ∧
        ¬ ∃ u, FalseLitOn x (Φ.get d) u ∧ HasSmallCFT Φ I0 x u (Real.log k ^ 6) s.U
  have hsub : s.J ⊆ D ∪ N := by
    intro c hc
    by_cases hw : c ∈ D
    · exact Finset.mem_union_left _ hw
    · exact Finset.mem_union_right _ (audit_matching_nonweak_counted k Φ I0 x s hx hcert hcover c hc hw)
  have h := Finset.card_le_card hsub
  have h2 := Finset.card_union_le D N
  have hn : N.card = NoTree k Φ I0 x s.U := by
    unfold NoTree
    apply congrArg Finset.card
    ext c
    simp [N]
  have hbound : s.J.card ≤ D.card + N.card := by omega
  simpa [D, hn] using hbound

/-- The source's matching-count bound holds at every reached Repair state. -/
theorem audit_reached_matching_count {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ) (hx : x ∈ sols (subF Φ I0))
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    s.J.card ≤ (omittedWeak Φ I0 x).card + NoTree k Φ I0 x s.U := by
  have hcert := audit_reach_no_tree_certificate k Φ I0 x W s j h
  have hcover := audit_reach_matching_assigned_covered k Φ I0 x W s j h
  exact audit_matching_card_le_weak_add_notree k Φ I0 x s hx hcert hcover

/-- Immediately before an augmentation, the selected clause is included in the count. -/
theorem audit_pending_matching_count {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ) (c : Fin Φ.length)
    (hx : x ∈ sols (subF Φ I0))
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (hpending : s.Pending c)
    (hnotree : ¬ ∃ T : ForcingTree Φ x, IsSmallTree k Φ I0 x T ∧
      T.root ∈ vbl (Φ.get c) ∧ Disjoint T.vars s.U) :
    (insert c s.J).card ≤ (omittedWeak Φ I0 x).card + NoTree k Φ I0 x s.U := by
  let t : RState Φ x := { s with J := insert c s.J }
  have hcert : audit_no_tree_certificate k Φ I0 x t := by
    intro d hd
    change d ∈ insert c s.J at hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hnotree
    · exact audit_reach_no_tree_certificate k Φ I0 x W s j h d hd
  have hcover : ∀ d ∈ t.J, satSet x (Φ.get d) ⊆ t.U := by
    intro d hd
    change d ∈ insert c s.J at hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hpending.2
    · exact audit_reach_matching_assigned_covered k Φ I0 x W s j h d hd
  simpa [t] using audit_matching_card_le_weak_add_notree k Φ I0 x t hx hcert hcover

end KSATSingleFlip.Connect


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



open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- Quantitative no-failure criterion combining the matching count, the first
repair bound, and the local-sparsity Hall argument. -/
theorem audit_repair_no_fail_from_bounds {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ) (c : Fin Φ.length)
    (hx : x ∈ sols (subF Φ I0))
    (hreach : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (hk : 4 ≤ k) (hscope : ∀ c : Fin Φ.length, (vbl (Φ.get c)).Nonempty)
    (hLS : LS k Φ) (hBounds : RepairBounds k Φ I0 x)
    (hD : ((omittedWeak Φ I0 x).card : ℝ) ≤ rho k ^ 4 * n)
    (hU : (s.U.card : ℝ) ≤ rho k * n)
    (hnum : 2 * (rho k ^ 4 * n + max (rho k ^ 4 * n)
       (s.U.card / (1024 * Real.log k ^ 20))) ≤ rho k * n) :
    ¬ RStep k Φ I0 x s c none := by
  intro hstep
  have hpend := hstep.1
  have hnotree : ¬ ∃ T : ForcingTree Φ x, IsSmallTree k Φ I0 x T ∧
      T.root ∈ vbl (Φ.get c) ∧ Disjoint T.vars s.U := by
    obtain ⟨_, htree | hmatch⟩ := hstep
    · obtain ⟨T, _, _, _, heq⟩ := htree
      contradiction
    · exact hmatch.1
  have hcount := audit_pending_matching_count k Φ I0 x W s j c hx hreach hpend hnotree
  have hcountR : ((insert c s.J).card : ℝ) ≤
      (omittedWeak Φ I0 x).card + NoTree k Φ I0 x s.U := by exact_mod_cast hcount
  have hbound := hBounds.1 s.U hU
  have hsmall : (2 * (insert c s.J).card : ℝ) ≤ rho k * n := by linarith
  exact audit_no_fail_of_small_matching k Φ I0 x s c hk hscope hLS hsmall hstep

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- The explicit numerical side condition needed by the no-failure bound follows
from elementary inequalities on ρ and log(k). -/
theorem audit_repair_no_fail_numeric {n : ℕ} (k : ℕ) (U : Finset (Fin n))
    (hlog : 1 ≤ Real.log k) (hrho : 0 ≤ rho k)
    (hrhosmall : 4 * rho k ^ 4 ≤ rho k)
    (hU : (U.card : ℝ) ≤ rho k * n) :
    2 * (rho k ^ 4 * n + max (rho k ^ 4 * n)
      (U.card / (1024 * Real.log k ^ 20))) ≤ rho k * n := by
  have hpow : 1 ≤ Real.log k ^ 20 := one_le_pow₀ hlog
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hprod : 4 * (rho k ^ 4 * n) ≤ rho k * n := by nlinarith
  have hden : (0 : ℝ) < 1024 * Real.log k ^ 20 := by positivity
  have hquot : 4 * ((U.card : ℝ) / (1024 * Real.log k ^ 20)) ≤ rho k * n := by
    have hnn : 0 ≤ rho k * n := mul_nonneg hrho hn
    have hmul : (U.card : ℝ) ≤ (rho k * n / 4) * (1024 * Real.log k ^ 20) := by
      nlinarith
    have hq : (U.card : ℝ) / (1024 * Real.log k ^ 20) ≤ rho k * n / 4 :=
      (div_le_iff₀ hden).mpr hmul
    linarith
  have hmax : 4 * max (rho k ^ 4 * n)
      (U.card / (1024 * Real.log k ^ 20)) ≤ rho k * n := by
    rcases le_total (rho k ^ 4 * n) (U.card / (1024 * Real.log k ^ 20)) with h | h
    · rw [max_eq_right h]; exact hquot
    · rw [max_eq_left h]; exact hprod
  linarith

/-- For positive k with log k ≥ 1, the paper's ρ is small enough for
its local non-failure arithmetic. -/
theorem audit_rho_small (k : ℕ) (hk : 4 ≤ k) (hlog : 1 ≤ Real.log k) :
    0 ≤ rho k ∧ 4 * rho k ^ 4 ≤ rho k := by
  have hkreal : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hceil : 0 < ⌈Real.log k ^ 6⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hexp : 1 ≤ 100 * ⌈Real.log k ^ 6⌉₊ := by omega
  have hpow : (k : ℝ) ≤ (k : ℝ) ^ (100 * ⌈Real.log k ^ 6⌉₊) := by
    simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ k by linarith) hexp
  have hquarter : rho k ≤ 1 / 4 := by
    unfold rho
    exact one_div_le_one_div_of_le (by norm_num) (le_trans hkreal hpow)
  have hrho : 0 ≤ rho k := by unfold rho; positivity
  have hsq : rho k ^ 2 ≤ rho k / 4 := by
    have h := mul_nonneg hrho (show 0 ≤ 1 / 4 - rho k by linarith)
    nlinarith
  have hsqone : rho k ^ 2 ≤ 1 := by nlinarith
  have hfour : rho k ^ 4 ≤ rho k ^ 2 := by
    have h := mul_nonneg (sq_nonneg (rho k)) (show 0 ≤ 1 - rho k ^ 2 by linarith)
    nlinarith [sq_nonneg (rho k)]
  constructor
  · exact hrho
  · linarith

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

/-- Repair cannot fail while its repair set is small under local sparsity and the source bounds. -/
theorem solution {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ) (c : Fin Φ.length)
    (hx : x ∈ sols (subF Φ I0))
    (hreach : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (hk : 4 ≤ k) (hlog : 1 ≤ Real.log k)
    (hscope : ∀ c : Fin Φ.length, (vbl (Φ.get c)).Nonempty)
    (hLS : LS k Φ) (hBounds : RepairBounds k Φ I0 x)
    (hD : ((omittedWeak Φ I0 x).card : ℝ) ≤ rho k ^ 4 * n)
    (hU : (s.U.card : ℝ) ≤ rho k * n) :
    ¬ RStep k Φ I0 x s c none := by
  obtain ⟨hrho, hsmall⟩ := audit_rho_small k hk hlog
  have hnum := audit_repair_no_fail_numeric k s.U hlog hrho hsmall hU
  exact audit_repair_no_fail_from_bounds k Φ I0 x W s j c hx hreach hk hscope hLS hBounds hD hU hnum

#print axioms solution
