-- Prove2me | solution 1 for Nock.Verb.den_local_opcode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:19.607815+00:00
-- url     : https://prove2.me/submissions/c745e978-8f48-433e-8d4b-f3ce84dd4c75

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_Den_leaf
public import Theorems.Thm_Nock_Verb_Den_null
public import Theorems.Thm_Nock_Verb_Den_star
public import Theorems.Thm_Nock_Verb_Den_slot
public import Theorems.Thm_Nock_Verb_Den_equal
public import Theorems.Thm_Nock_Verb_Den_minus
public import Theorems.Thm_Nock_Verb_Den_edit_node
public import Theorems.Thm_Nock_Verb_EvN_autocons
public import Theorems.Thm_Nock_Verb_EvN_op0
public import Theorems.Thm_Nock_Verb_EvN_op1
public import Theorems.Thm_Nock_Verb_EvN_op2
public import Theorems.Thm_Nock_Verb_EvN_op3
public import Theorems.Thm_Nock_Verb_EvN_op4
public import Theorems.Thm_Nock_Verb_EvN_op5
public import Theorems.Thm_Nock_Verb_EvN_op7
public import Theorems.Thm_Nock_Verb_EvN_op8
public import Theorems.Thm_Nock_Verb_EvN_op10
public import Theorems.Thm_Nock_Verb_EvN_op6
public import Theorems.Thm_Nock_Verb_EvN_op9
public import Theorems.Thm_Nock_Verb_Den_terminal_iff
public import Theorems.Thm_Nock_Verb_slot_one
public import Theorems.Thm_Nock_Verb_slot_two
public import Theorems.Thm_Nock_Verb_slot_three
public import Theorems.Thm_Nock_Verb_slot_two_atom
public import Theorems.Thm_Nock_Verb_slot_three_atom
public import Theorems.Thm_Nock_Verb_lus_atom
public import Theorems.Thm_Nock_Verb_slot_pair_some
section
@[expose] public section
namespace Nock
namespace Verb
open Noun
private theorem denotation_conditional_reduction {r₀ : Verb} {x : Noun} (n1 n2 : Verb) (htn2 :
  n2.isTerminal = true)
  (hn1 : ∀ (v : Noun), n1.Den v ↔ v = n1.noun)
  (star_term : ∀ (W : Verb) (p : Noun), W.isTerminal = true → ((node Action.star n1 W).Den p ↔ Ev
    n1.noun W.noun p))
  (hr :
    (match (generalizing := false) n2 with
      | node _ b c =>
        some
          (node Action.star n1
            (node Action.star c
              (node Action.null (leaf 0)
                (node Action.star (node Action.null (leaf 2) (leaf 3))
                  (node Action.null (leaf 0)
                    (node Action.star n1 (node Action.null (leaf 4) (node Action.null (leaf 4)
                      b))))))))
      | _ => none) =
      some r₀) :
  Ev n1.noun ((atom 6).cell n2.noun) x ↔ r₀.Den x := by
  cases n2 with
  | leaf => simp at hr
  | node bn b c =>
      obtain rfl := Option.some.inj hr
      simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
      obtain ⟨⟨_, htb⟩, htc⟩ := htn2
      have dStar : ∀ (W : Verb) y,
          (Den (Verb.node .star n1 W) y ↔ ∃ q, Den W q ∧ Ev n1.noun q y) := by
        intro W y; rw [Den_star]
        exact ⟨fun ⟨p,q,hp,hq,hev⟩ => ⟨q, hq, (hn1 p).1 hp ▸ hev⟩,
               fun ⟨q,hq,hev⟩ => ⟨n1.noun, q, (hn1 _).2 rfl, hq, hev⟩⟩
      have dStarC : ∀ (W : Verb) y,
          (Den (Verb.node .star c W) y ↔ ∃ q, Den W q ∧ Ev c.noun q y) := by
        intro W y; rw [Den_star]
        exact ⟨fun ⟨p,q,hp,hq,hev⟩ => ⟨q, hq, (Den_terminal_iff htc).1 hp ▸ hev⟩,
               fun ⟨q,hq,hev⟩ => ⟨c.noun, q, (Den_terminal_iff htc).2 rfl, hq, hev⟩⟩
      have hIarg : isTerminal (Verb.node .null (.leaf 4) (.node .null (.leaf 4) b)) = true := by
        simp [isTerminal, Action.isNull, htb]
      rw [EvN_op6]
      constructor
      · -- EvN_op6 ⇒ Den (macro)
        rintro ⟨B, C, D, cv, heq, hcv, hor⟩
        obtain ⟨hBeq, hCDeq⟩ := Noun.cell.inj heq
        subst hBeq
        rcases hor with ⟨rfl, hCx⟩ | ⟨rfl, hDx⟩
        · -- cv = 0 → head arm
          refine (dStar _ _).2 ⟨C, ?_, hCx⟩
          refine (dStarC _ _).2 ⟨Noun.cell (.atom 0) (.atom 2), ?_,
                  (EvN_op0).2 ⟨2, rfl, hCDeq ▸ slot_two⟩⟩
          refine (Den_null).2 ⟨.atom 0, .atom 2, rfl, Den_leaf.2 rfl, ?_⟩
          refine (Den_star).2 ⟨Noun.cell (.atom 2) (.atom 3), Noun.cell (.atom 0) (.atom 2),
                  (Den_null).2 ⟨.atom 2, .atom 3, rfl, Den_leaf.2 rfl, Den_leaf.2 rfl⟩, ?_,
                  (EvN_op0).2 ⟨2, rfl, slot_two⟩⟩
          refine (Den_null).2 ⟨.atom 0, .atom 2, rfl, Den_leaf.2 rfl, ?_⟩
          refine (dStar _ _).2 ⟨_, (Den_terminal_iff hIarg).2 rfl, ?_⟩
          exact (EvN_op4).2 ⟨.atom 1, (EvN_op4).2 ⟨.atom 0, hcv, lus_atom⟩, lus_atom⟩
        · -- cv = 1 → tail arm
          refine (dStar _ _).2 ⟨D, ?_, hDx⟩
          refine (dStarC _ _).2 ⟨Noun.cell (.atom 0) (.atom 3), ?_,
                  (EvN_op0).2 ⟨3, rfl, hCDeq ▸ slot_three⟩⟩
          refine (Den_null).2 ⟨.atom 0, .atom 3, rfl, Den_leaf.2 rfl, ?_⟩
          refine (Den_star).2 ⟨Noun.cell (.atom 2) (.atom 3), Noun.cell (.atom 0) (.atom 3),
                  (Den_null).2 ⟨.atom 2, .atom 3, rfl, Den_leaf.2 rfl, Den_leaf.2 rfl⟩, ?_,
                  (EvN_op0).2 ⟨3, rfl, slot_three⟩⟩
          refine (Den_null).2 ⟨.atom 0, .atom 3, rfl, Den_leaf.2 rfl, ?_⟩
          refine (dStar _ _).2 ⟨_, (Den_terminal_iff hIarg).2 rfl, ?_⟩
          exact (EvN_op4).2 ⟨.atom 2, (EvN_op4).2 ⟨.atom 1, hcv, lus_atom⟩, lus_atom⟩
      · -- Den (macro) ⇒ EvN_op6
        intro hmacro
        obtain ⟨qa0, ha0, hC4⟩ := (dStar _ _).1 hmacro
        obtain ⟨qb0, hb0, hC3⟩ := (dStarC _ _).1 ha0
        rw [Den_null] at hb0; obtain ⟨v0, vc0, rfl, hv0, hc0⟩ := hb0
        rw [Den_leaf] at hv0; subst hv0
        rw [Den_star] at hc0; obtain ⟨p23, qd0, hp23, hd0, hC2⟩ := hc0
        rw [Den_null] at hp23; obtain ⟨w2, w3, rfl, hw2, hw3⟩ := hp23
        rw [Den_leaf] at hw2 hw3; subst hw2; subst hw3
        rw [Den_null] at hd0; obtain ⟨u0, vinner, rfl, hu0, hinner⟩ := hd0
        rw [Den_leaf] at hu0; subst hu0
        rw [star_term _ _ hIarg] at hinner
        obtain ⟨y, hy1, hly⟩ := (EvN_op4).1 hinner
        obtain ⟨z, hz1, hlz⟩ := (EvN_op4).1 hy1
        cases z with
        | cell => simp [Noun.lus] at hlz
        | atom k =>
            rw [lus_atom] at hlz; obtain rfl := Option.some.inj hlz
            rw [lus_atom] at hly; obtain rfl := Option.some.inj hly
            obtain ⟨ax, hax, hs23⟩ := (EvN_op0).1 hC2
            have haxv : ax = k + 2 := by injection hax with h; omega
            subst haxv
            rcases slot_pair_some _ _ hs23 with h1 | h2 | h3
            · omega
            · -- k = 0
              have hk : k = 0 := by omega
              subst hk
              rw [slot_two] at hs23; obtain rfl := Option.some.inj hs23
              obtain ⟨ax', hax', hs3⟩ := (EvN_op0).1 hC3
              have : ax' = 2 := by injection hax' with h; omega
              subst this
              cases hcn : c.noun with
              | atom => rw [hcn, slot_two_atom] at hs3; simp at hs3
              | cell C D =>
                  rw [hcn, slot_two] at hs3; obtain rfl := Option.some.inj hs3
                  exact ⟨b.noun, C, D, .atom 0, rfl, hz1, Or.inl ⟨rfl, hC4⟩⟩
            · -- k = 1
              have hk : k = 1 := by omega
              subst hk
              rw [slot_three] at hs23; obtain rfl := Option.some.inj hs23
              obtain ⟨ax', hax', hs3⟩ := (EvN_op0).1 hC3
              have : ax' = 3 := by injection hax' with h; omega
              subst this
              cases hcn : c.noun with
              | atom => rw [hcn, slot_three_atom] at hs3; simp at hs3
              | cell C D =>
                  rw [hcn, slot_three] at hs3; obtain rfl := Option.some.inj hs3
                  exact ⟨b.noun, C, D, .atom 1, rfl, hz1, Or.inr ⟨rfl, hC4⟩⟩
private theorem denotation_composition_reduction {r₀ : Verb} {x : Noun} (n1 n2 : Verb) (htn2 :
  n2.isTerminal = true)
  (star_term : ∀ (W : Verb) (p : Noun), W.isTerminal = true → ((node Action.star n1 W).Den p ↔ Ev
    n1.noun W.noun p))
  (hr :
    (match (generalizing := false) n2 with
      | node _ b c => some (node Action.star (node Action.star n1 b) (node Action.star n1 c))
      | _ => none) =
      some r₀) :
  Ev n1.noun ((atom 2).cell n2.noun) x ↔ r₀.Den x := by
  cases n2 with
  | leaf => simp at hr
  | node bn b c =>
      obtain rfl := Option.some.inj hr
      simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
      obtain ⟨⟨_, htb⟩, htc⟩ := htn2
      rw [EvN_op2, Den_star]
      constructor
      · rintro ⟨hb, hc, sb, sc, heq, hsb, hsc, hev⟩
        obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
        exact ⟨sb, sc, (star_term _ _ htb).2 hsb, (star_term _ _ htc).2 hsc, hev⟩
      · rintro ⟨sb, sc, hsb, hsc, hev⟩
        exact ⟨b.noun, c.noun, sb, sc, rfl, (star_term _ _ htb).1 hsb,
               (star_term _ _ htc).1 hsc, hev⟩
end Verb
end Nock
end
end

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {sub r₀ x} (hd : inOpcodeDomain sub = true) (hr : reduce sub = some r₀) :
    (Den sub x ↔ Den r₀ x) := by
  cases sub with
  | leaf => simp [inOpcodeDomain] at hd
  | node a n1 t =>
    cases t with
    | leaf => cases a <;> simp [inOpcodeDomain] at hd
    | node ra i n2 =>
      cases a with
      | null => simp [inOpcodeDomain] at hd
      | wut => simp [inOpcodeDomain] at hd
      | equal => simp [inOpcodeDomain] at hd
      | slot => simp [inOpcodeDomain] at hd
      | edit => simp [inOpcodeDomain] at hd
      | minus => simp [inOpcodeDomain] at hd
      | star =>
        simp only [inOpcodeDomain, Bool.and_eq_true] at hd
        obtain ⟨⟨⟨⟨htn1, hra⟩, hti⟩, htn2⟩, hhead⟩ := hd
        have htt : isTerminal (Verb.node ra i n2) = true := by
          simp only [isTerminal, Bool.and_eq_true]; exact ⟨⟨hra, hti⟩, htn2⟩
        have hn1 : ∀ v, Den n1 v ↔ v = n1.noun := fun v => Den_terminal_iff htn1
        have hn2 : ∀ v, Den n2 v ↔ v = n2.noun := fun v => Den_terminal_iff htn2
        have star_term : ∀ (W : Verb) (p : Noun), isTerminal W = true →
            (Den (Verb.node .star n1 W) p ↔ Ev n1.noun W.noun p) := by
          intro W p htW
          rw [Den_star]
          constructor
          · rintro ⟨va, vb, hva, hvb, hev⟩
            rw [(Den_terminal_iff htn1).1 hva, (Den_terminal_iff htW).1 hvb] at hev; exact hev
          · intro hev
            exact ⟨n1.noun, W.noun, (Den_terminal_iff htn1).2 rfl, (Den_terminal_iff htW).2 rfl,
              hev⟩
        have hsub : (Den (Verb.node .star n1 (.node ra i n2)) x
                     ↔ Ev n1.noun (Noun.cell i.noun n2.noun) x) := by
          rw [star_term (Verb.node ra i n2) x htt]; simp only [noun]
        rw [hsub]
        rw [reduce] at hr
        cases i with
        | node bi ic id =>
            rw [redex] at hr
            obtain rfl := Option.some.inj hr
            simp only [noun]
            rw [Den_null, EvN_autocons]
            constructor
            · rintro ⟨l, r, rfl, hl, hr⟩
              refine ⟨l, r, rfl, (star_term _ _ hti).2 ?_, (star_term _ _ htn2).2 hr⟩
              simpa [noun] using hl
            · rintro ⟨p, q, rfl, hp, hq⟩
              refine ⟨p, q, rfl, ?_, (star_term _ _ htn2).1 hq⟩
              have := (star_term (Verb.node bi ic id) p hti).1 hp
              simpa [noun] using this
        | leaf op =>
            simp only [noun]
            simp only [redex] at hr
            split at hr
            · -- op 0
              obtain rfl := Option.some.inj hr
              rw [EvN_op0, Den_slot]
              constructor
              · rintro ⟨ax, hax, hs⟩; exact ⟨ax, n1.noun, (hn2 _).2 hax.symm, (hn1 _).2 rfl, hs⟩
              · rintro ⟨ax, b, hax, hb, hs⟩
                rw [(hn1 _).1 hb] at hs; exact ⟨ax, ((hn2 _).1 hax).symm, hs⟩
            · -- op 1
              obtain rfl := Option.some.inj hr
              rw [EvN_op1]; exact (hn2 x).symm
            · -- op 2
              exact denotation_composition_reduction n1 n2 htn2 star_term hr
            · -- op 3
              obtain rfl := Option.some.inj hr
              rw [EvN_op3, Den_minus]
              constructor
              · rintro ⟨y, hy, rfl⟩
                exact ⟨y, (star_term _ _ htn2).2 hy, Or.inl ⟨(Den_leaf).2 rfl, rfl⟩⟩
              · rintro ⟨b, hb, hor⟩
                rcases hor with ⟨_, rfl⟩ | ⟨h4, _⟩
                · exact ⟨b, (star_term _ _ htn2).1 hb, rfl⟩
                · exact absurd ((Den_leaf).1 h4) (by decide)
            · -- op 4
              obtain rfl := Option.some.inj hr
              rw [EvN_op4, Den_minus]
              constructor
              · rintro ⟨y, hy, hlus⟩
                exact ⟨y, (star_term _ _ htn2).2 hy, Or.inr ⟨(Den_leaf).2 rfl, hlus⟩⟩
              · rintro ⟨b, hb, hor⟩
                rcases hor with ⟨h3, _⟩ | ⟨_, hlus⟩
                · exact absurd ((Den_leaf).1 h3) (by decide)
                · exact ⟨b, (star_term _ _ htn2).1 hb, hlus⟩
            · -- op 5
              cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  rw [EvN_op5, Den_equal]
                  constructor
                  · rintro ⟨hb, hc, sb, sc, heq, hsb, hsc, rfl⟩
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
                    exact ⟨sb, sc, (star_term _ _ htb).2 hsb, (star_term _ _ htc).2 hsc, rfl⟩
                  · rintro ⟨sb, sc, hsb, hsc, rfl⟩
                    exact ⟨b.noun, c.noun, sb, sc, rfl, (star_term _ _ htb).1 hsb,
                           (star_term _ _ htc).1 hsc, rfl⟩
            · -- op 6  (if-then-else macro; main.tex:1067)
              exact denotation_conditional_reduction n1 n2 htn2 hn1 star_term hr
            · -- op 7
              cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  rw [EvN_op7, Den_star]
                  constructor
                  · rintro ⟨hb, hc, sb, heq, hsb, hev⟩
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
                    exact ⟨sb, c.noun, (star_term _ _ htb).2 hsb, (Den_terminal_iff htc).2 rfl, hev⟩
                  · rintro ⟨p, q, hp, hq, hev⟩
                    rw [(Den_terminal_iff htc).1 hq] at hev
                    exact ⟨b.noun, c.noun, p, rfl, (star_term _ _ htb).1 hp, hev⟩
            · -- op 8
              cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  rw [EvN_op8, Den_star]
                  constructor
                  · rintro ⟨hb, hc, sb, heq, hsb, hev⟩
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
                    refine ⟨Noun.cell sb n1.noun, c.noun, ?_, (Den_terminal_iff htc).2 rfl, hev⟩
                    rw [Den_null]
                    exact ⟨sb, n1.noun, rfl, (star_term _ _ htb).2 hsb, (hn1 _).2 rfl⟩
                  · rintro ⟨p, q, hp, hq, hev⟩
                    rw [Den_null] at hp
                    obtain ⟨pb, pn, rfl, hpb, hpn⟩ := hp
                    rw [(hn1 _).1 hpn] at hev
                    rw [(Den_terminal_iff htc).1 hq] at hev
                    exact ⟨b.noun, c.noun, pb, rfl, (star_term _ _ htb).1 hpb, hev⟩
            · -- op 9
              cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  have htform : isTerminal (Verb.node .null (.leaf 2)
                      (.node .null (.node .null (.leaf 0) (.leaf 1)) (.node .null (.leaf 0) b))) =
                        true := by
                    simp [isTerminal, Action.isNull, htb]
                  rw [EvN_op9, Den_star]
                  constructor
                  · rintro ⟨ax, c', core, arm, heq, hcore, hslot, hev⟩
                    obtain ⟨hbn, rfl⟩ := Noun.cell.inj heq
                    refine ⟨core, _, (star_term c core htc).2 hcore,
                            (Den_terminal_iff htform).2 rfl, ?_⟩
                    refine (EvN_op2).2 ⟨_, _, core, arm, rfl, ?_, ?_, hev⟩
                    · exact (EvN_op0).2 ⟨1, rfl, slot_one⟩
                    · exact (EvN_op0).2 ⟨ax, hbn, hslot⟩
                  · rintro ⟨p, q, hp, hq, hev⟩
                    have hp' := (star_term c p htc).1 hp
                    rw [(Den_terminal_iff htform).1 hq] at hev
                    obtain ⟨hb2, hc2, sb, sc, heq2, hsb, hsc, hev2⟩ := (EvN_op2).1 hev
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq2
                    obtain ⟨ax1, hax1, hs1⟩ := (EvN_op0).1 hsb
                    obtain ⟨ax2, hax2, hs2⟩ := (EvN_op0).1 hsc
                    have hax1' : ax1 = 1 := by injection hax1 with h; omega
                    rw [hax1', slot_one] at hs1; obtain rfl := Option.some.inj hs1
                    exact ⟨ax2, c.noun, p, sc, by rw [hax2], hp', hs2, hev2⟩
            · -- op 10
              cases n2 with
              | leaf => simp at hr
              | node bn hd d =>
                  cases hd with
                  | leaf => simp at hr
                  | node bhd ax c =>
                      obtain rfl := Option.some.inj hr
                      simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                      obtain ⟨⟨_, ⟨_, htax⟩, htc⟩, htd⟩ := htn2
                      have hax : ∀ v, Den ax v ↔ v = ax.noun := fun v => Den_terminal_iff htax
                      rw [EvN_op10, Den_edit_node]
                      constructor
                      · rintro ⟨axv, cc, dd, new, old, heq, hnew, hold, hedit⟩
                        obtain ⟨heq1, rfl⟩ := Noun.cell.inj heq
                        obtain ⟨haxn, rfl⟩ := Noun.cell.inj heq1
                        exact ⟨axv, new, old, (hax _).2 haxn.symm, (star_term _ _ htc).2 hnew,
                               (star_term _ _ htd).2 hold, hedit⟩
                      · rintro ⟨axv, n, o, haxd, hn, ho, hedit⟩
                        refine ⟨axv, c.noun, d.noun, n, o, ?_, (star_term _ _ htc).1 hn,
                                (star_term _ _ htd).1 ho, hedit⟩
                        rw [(hax _).1 haxd]
            · -- default
              simp at hr
end Nock.Verb
