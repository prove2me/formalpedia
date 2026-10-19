-- Prove2me | solution 1 for OAI.LinearListHadwiger.Stage.two_districts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:56:34.796973+00:00
-- url     : https://prove2.me/submissions/6d045533-8876-4653-90bb-c3a37b4e087f

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000
import Theorems.Thm_OAI_LinearListHadwiger_SmallList_additive_deletion_or_obstruction

section
-- module Solutions.OAIQW_ListHadwiger.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

theorem choosable_mono {V : Type} {G : SimpleGraph V} {k l : ℕ}
    (h : Choosable G k) (hkl : k ≤ l) : Choosable G l := by
  intro Color L hL
  exact h Color L (fun v => hkl.trans (hL v))

theorem choosable_card {V : Type} [Fintype V] (G : SimpleGraph V) :
    Choosable G (Fintype.card V) := by
  classical
  intro Color L hL
  have hall : ∀ s : Finset V, s.card ≤ (s.biUnion L).card := by
    intro s
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    obtain ⟨v, hv⟩ := hs
    exact (Finset.card_le_univ s).trans ((hL v).trans
      (Finset.card_le_card (Finset.subset_biUnion_of_mem L hv)))
  obtain ⟨c, hc, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective L).mp hall
  exact ⟨c, hmem, fun _ _ hvw heq => hvw.ne (hc heq)⟩

theorem choosable_listChromaticNumber {V : Type} [Fintype V] (G : SimpleGraph V) :
    Choosable G (listChromaticNumber G) := by
  exact Nat.sInf_mem (s := {k : ℕ | Choosable G k})
    ⟨Fintype.card V, choosable_card G⟩

theorem listChromaticNumber_le_iff {V : Type} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) : listChromaticNumber G ≤ k ↔ Choosable G k := by
  constructor
  · exact fun h => choosable_mono (choosable_listChromaticNumber G) h
  · intro h
    exact Nat.sInf_le h

theorem cliqueMinor_order_le_card {V : Type} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (h : HasCliqueMinor G t) : t ≤ Fintype.card V := by
  classical
  obtain ⟨B, hc, hd, _⟩ := h
  have hb : ∀ i, ∃ v, v ∈ B i := fun i => by
    obtain ⟨v⟩ := (hc i).nonempty
    exact ⟨v.val, v.property⟩
  choose v hv using hb
  have hi : Function.Injective v := by
    intro i j hij
    by_contra hn
    exact Set.disjoint_left.mp (hd i j hn) (hv i) (by
      rw [hij]
      exact hv j)
  simpa using Fintype.card_le_of_injective v hi

theorem cliqueMinor_zero {V : Type} (G : SimpleGraph V) : HasCliqueMinor G 0 := by
  refine ⟨Fin.elim0, ?_, ?_, ?_⟩
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i

theorem hadwiger_bddAbove {V : Type} [Fintype V] (G : SimpleGraph V) :
    BddAbove {t : ℕ | HasCliqueMinor G t} :=
  ⟨Fintype.card V, fun _ h => cliqueMinor_order_le_card h⟩

theorem cliqueMinor_le_hadwigerNumber {V : Type} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (h : HasCliqueMinor G t) : t ≤ hadwigerNumber G :=
  le_csSup (hadwiger_bddAbove G) h

theorem hasCliqueMinor_hadwigerNumber {V : Type} [Fintype V] (G : SimpleGraph V) :
    HasCliqueMinor G (hadwigerNumber G) := by
  exact Nat.sSup_mem ⟨0, cliqueMinor_zero G⟩ (hadwiger_bddAbove G)

theorem cliqueMinor_one {V : Type} [Nonempty V] (G : SimpleGraph V) :
    HasCliqueMinor G 1 := by
  classical
  let v : V := Classical.choice inferInstance
  refine ⟨fun _ => {v}, ?_, ?_, ?_⟩
  · intro i
    exact SimpleGraph.Connected.of_subsingleton
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

lemma exists_separator {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) {k : ℕ} (hord : k < S.card) (hn : ¬KConnectedOn G S k) :
    ∃ V₁ Z V₂, Z.card < k ∧ SeparatorSplit G S V₁ Z V₂ := by
  classical
  obtain ⟨Z, hZS, hZk, hZ⟩ : ∃ Z ⊆ S,
      Z.card < k ∧ ¬(G.induce (↑(S \ Z) : Set V)).Connected := by
    simpa only [KConnectedOn, not_and, hord, forall_const, not_forall,
      exists_prop, Classical.not_imp] using hn
  let T := S \ Z
  let H := G.induce (↑T : Set V)
  have hT : T.Nonempty := by
    have heq := Finset.card_sdiff_add_card_eq_card hZS
    exact Finset.card_pos.mp (by dsimp [T]; omega)
  have hnpre : ¬H.Preconnected := by
    intro h
    apply hZ
    obtain ⟨v, hv⟩ := hT
    exact { preconnected := h, nonempty := ⟨⟨v, hv⟩⟩ }
  obtain ⟨u, v, huv⟩ : ∃ u v, ¬H.Reachable u v := by
    simpa only [SimpleGraph.Preconnected, not_forall] using hnpre
  let V₁ := T.filter (fun x => ∃ hx : x ∈ T, H.Reachable u ⟨x, hx⟩)
  let V₂ := T \ V₁
  have h₁T : V₁ ⊆ T := Finset.filter_subset _ _
  have h₂T : V₂ ⊆ T := Finset.sdiff_subset
  have hu : u.val ∈ V₁ := by
    exact Finset.mem_filter.mpr ⟨u.property, u.property, SimpleGraph.Reachable.rfl⟩
  have hv : v.val ∈ V₂ := by
    refine Finset.mem_sdiff.mpr ⟨v.property, ?_⟩
    intro h
    obtain ⟨_, hx, hr⟩ := Finset.mem_filter.mp h
    exact huv hr
  refine ⟨V₁, Z, V₂, hZk, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ⟨u.val, hu⟩, ⟨v.val, hv⟩, ?_⟩
  · ext x
    simp only [Finset.mem_union]
    have hsub : x ∈ V₁ → x ∈ S ∧ x ∉ Z := fun hx => Finset.mem_sdiff.mp (h₁T hx)
    have hZsub : x ∈ Z → x ∈ S := fun hx => hZS hx
    simp only [V₂, T, Finset.mem_sdiff]
    tauto
  · exact Finset.disjoint_left.mpr (fun x hx hz => (Finset.mem_sdiff.mp (h₁T hx)).2 hz)
  · exact Finset.disjoint_left.mpr (fun x hx hx₂ => (Finset.mem_sdiff.mp hx₂).2 hx)
  · exact Finset.disjoint_left.mpr (fun x hz hx => (Finset.mem_sdiff.mp (h₂T hx)).2 hz)
  · intro x hx y hy hxy
    obtain ⟨_, hxT, hr⟩ := Finset.mem_filter.mp hx
    have hyT := h₂T hy
    have hay : H.Adj ⟨x, hxT⟩ ⟨y, hyT⟩ := hxy
    have hy₁ : y ∈ V₁ := Finset.mem_filter.mpr ⟨hyT, hyT, hr.trans hay.reachable⟩
    exact (Finset.mem_sdiff.mp hy).2 hy₁

lemma choosable_of_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {k : ℕ} (h : Choosable H k) : Choosable G k := by
  intro Color L hL
  obtain ⟨c, hc, hp⟩ := h Color (fun w => L (e.symm w)) (fun w => hL (e.symm w))
  refine ⟨fun v => c (e v), ?_, ?_⟩
  · intro v
    simpa using hc (e v)
  · intro v w hvw
    exact hp (e.map_adj_iff.mpr hvw)

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Connectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

open scoped Classical

theorem degenerate_coloring_on {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (L : V → Finset Color) (φ : V → Color)
    {d : ℕ} (hdeg : DegenerateOn G S d) (hL : ∀ v ∈ S, d + 1 ≤ (L v).card) :
    ∃ c, ValidOn G S L c := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    obtain rfl | hS := S.eq_empty_or_nonempty
    · exact ⟨φ, by simp [ValidOn, ProperOn]⟩
    obtain ⟨v, hv, hvd⟩ := hdeg S (Finset.Subset.refl _) hS
    have herase : S.erase v ⊂ S := Finset.erase_ssubset hv
    obtain ⟨c, hc⟩ := ih (S.erase v) herase
      (fun T hT => hdeg T (hT.trans (Finset.erase_subset _ _)))
      (fun w hw => hL w (Finset.mem_of_mem_erase hw))
    let forbidden := (S.filter (G.Adj v)).image c
    have hfc : forbidden.card ≤ d := Finset.card_image_le.trans hvd
    have hpos : (L v \ forbidden).Nonempty := by
      apply Finset.card_pos.mp
      have hh := Finset.card_le_card_sdiff_add_card (s := L v) (t := forbidden)
      have hl := hL v hv
      omega
    obtain ⟨a, ha⟩ := hpos
    obtain ⟨haL, haF⟩ := Finset.mem_sdiff.mp ha
    let c' : V → Color := fun w => if w = v then a else c w
    have hcv : c' v = a := by simp [c']
    have hcw : ∀ w, w ≠ v → c' w = c w := fun w hw => ite_eq_right hw
    refine ⟨c', ?_, ?_⟩
    · intro w hw
      by_cases hwv : w = v
      · subst w
        rwa [hcv]
      · rw [hcw w hwv]
        exact hc.1 w (Finset.mem_erase.mpr ⟨hwv, hw⟩)
    · intro w hw z hz hadj
      by_cases hwv : w = v
      · subst w
        have hzv : z ≠ v := hadj.ne.symm
        rw [hcv, hcw z hzv]
        intro heq
        exact haF (Finset.mem_image.mpr
          ⟨z, Finset.mem_filter.mpr ⟨hz, hadj⟩, heq.symm⟩)
      · by_cases hzv : z = v
        · subst z
          rw [hcw w hwv, hcv]
          intro heq
          exact haF (Finset.mem_image.mpr
            ⟨w, Finset.mem_filter.mpr ⟨hw, hadj.symm⟩, heq⟩)
        · rw [hcw w hwv, hcw z hzv]
          exact hc.2 (Finset.mem_erase.mpr ⟨hwv, hw⟩)
            (Finset.mem_erase.mpr ⟨hzv, hz⟩) hadj

theorem choosable_of_degenerate {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d : ℕ} (hdeg : DegenerateOn G Finset.univ d) :
    Choosable G (d + 1) := by
  classical
  intro Color L hL
  have hn : ∀ v, (L v).Nonempty := by
    intro v
    apply Finset.card_pos.mp
    have hh := hL v
    omega
  choose φ hφ using hn
  obtain ⟨c, hc⟩ := degenerate_coloring_on G Finset.univ L φ hdeg (fun v _ => hL v)
  exact ⟨c, fun v => hc.1 v (Finset.mem_univ _),
    fun _ _ h => hc.2 (Finset.mem_univ _) (Finset.mem_univ _) h⟩

theorem listChromaticNumber_le_of_degenerate {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d : ℕ} (hdeg : DegenerateOn G Finset.univ d) :
    listChromaticNumber G ≤ d + 1 :=
  (listChromaticNumber_le_iff G _).mpr (choosable_of_degenerate G hdeg)

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.MinorModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger
open SimpleGraph PathPacking

namespace MinorModel
variable {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}

theorem lift_clique (M : MinorModel G H) {t : ℕ} (h : HasCliqueMinor H t) :
    HasCliqueMinor G t := by
  obtain ⟨B, hc, hd, he⟩ := h
  refine ⟨fun i => M.expand (B i), fun i => M.expand_connected (hc i),
    fun i j hij => M.expand_disjoint (hd i j hij), ?_⟩
  intro i j hij
  obtain ⟨a, ha, b, hb, hab⟩ := he i j hij
  obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hab
  exact ⟨x, ⟨a, ha, hx⟩, y, ⟨b, hb, hy⟩, hxy⟩

theorem hadwiger_le [Fintype V] [Fintype W] (M : MinorModel G H) :
    hadwigerNumber H ≤ hadwigerNumber G :=
  cliqueMinor_le_hadwigerNumber (M.lift_clique (hasCliqueMinor_hadwigerNumber H))

end MinorModel

open scoped Classical

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.ConnectivityTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

namespace ConnectivityTests

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

theorem finite_hitting {α β : Type} [Fintype α] [Fintype β]
    (s : ℕ) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (R : β → α → Prop) [DecidableRel R] (p : ℝ) (hp : 0 ≤ p)
    (hrow : ∀ v, ∑ a, w a * (if ¬R v a then 1 else 0) ≤ p)
    (hsmall : (Fintype.card β : ℝ) * p ^ s < 1) :
    ∃ f : Fin s → α, ∀ v, ∃ i, R v (f i) := by
  classical
  let m : (Fin s → α) → ℝ := fun f => ∏ i, w (f i)
  let bad : β → (Fin s → α) → ℝ := fun v f => if ∀ i, ¬R v (f i) then 1 else 0
  have hm : ∀ f, 0 ≤ m f := fun f => Finset.prod_nonneg fun i _ => hw (f i)
  have hnorm : ∑ f, m f = 1 := by
    dsimp [m]
    rw [← Fintype.prod_sum]
    simp [hs]
  have hevent (v : β) : ∑ f, m f * bad v f ≤ p ^ s := by
    calc
      ∑ f, m f * bad v f = ∏ i : Fin s, ∑ a, w a * (if ¬R v a then 1 else 0) := by
        rw [Fintype.prod_sum]
        apply Finset.sum_congr rfl
        intro f _
        simp only [Finset.prod_mul_distrib, Finset.prod_boole, Finset.mem_univ,
          forall_const, m, bad]
      _ ≤ ∏ _i : Fin s, p := by
        have hnonneg : 0 ≤ ∑ a, w a * (if ¬R v a then 1 else 0) :=
          Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (by split_ifs <;> norm_num)
        have hprod (T : Finset (Fin s)) :
            (∏ _i ∈ T, ∑ a, w a * (if ¬R v a then 1 else 0)) ≤ ∏ _i ∈ T, p := by
          induction T using Finset.induction_on with
          | empty => simp
          | @insert index T hindex ih =>
            simp only [Finset.prod_insert hindex]
            exact mul_le_mul (hrow v) ih (Finset.prod_nonneg fun _ _ => hnonneg) hp
        exact hprod Finset.univ
      _ = p ^ s := by simp
  by_contra h
  have hbad : ∀ f : Fin s → α, ∃ v, ∀ i, ¬R v (f i) := by
    simpa only [not_exists, not_forall] using h
  have hone : 1 ≤ ∑ f, ∑ v, m f * bad v f := by
    rw [← hnorm]
    apply Finset.sum_le_sum
    intro f _
    obtain ⟨v, hv⟩ := hbad f
    calc
      m f = m f * bad v f := by simp [bad, hv]
      _ ≤ ∑ v, m f * bad v f := Finset.single_le_sum (f := fun v => m f * bad v f)
        (fun v _ => mul_nonneg (hm f) (by dsimp [bad]; split_ifs <;> norm_num))
        (Finset.mem_univ _)
  have hupper : (∑ f, ∑ v, m f * bad v f) ≤ (Fintype.card β : ℝ) * p ^ s := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _v : β, p ^ s := Finset.sum_le_sum fun v _ => hevent v
      _ = _ := by simp
  linarith

lemma sum_uniform_mask (A D : Finset V) (z : ℝ) :
    (∑ a : V, (if a ∈ A then z else 0) * (if a ∈ D then 1 else 0)) =
      ((A ∩ D).card : ℝ) * z := by
  calc
    _ = ∑ a : V, if a ∈ A ∩ D then z else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ A <;> by_cases hd : a ∈ D <;> simp [ha, hd]
    _ = _ := by rw [Finset.sum_ite_mem]; simp

theorem exists_neighborhood_cover (G : SimpleGraph V) (A : Finset V) [DecidableRel G.Adj]
    {n k : ℝ} (hn : 1 ≤ n) (hk : 0 < k) (ha : A.Nonempty)
    (hAn : (A.card : ℝ) ≤ n)
    (hd : ∀ v ∈ A, k / 3 ≤ ((A.filter (G.Adj v)).card : ℝ)) :
    ∃ R ⊆ A, R.card ≤ ⌈10 * (n / k) * Real.log (2 * n)⌉₊ ∧
      ∀ v ∈ A, ∃ r ∈ R, G.Adj v r := by
  classical
  let s := ⌈10 * (n / k) * Real.log (2 * n)⌉₊
  let c : ℝ := A.card
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast Finset.card_pos.mpr ha
  have hcn : c ≤ n := hAn
  let w : V → ℝ := fun a => if a ∈ A then c⁻¹ else 0
  have hw : ∀ a, 0 ≤ w a := fun a => by dsimp [w]; positivity
  have hs : ∑ a, w a = 1 := by
    dsimp [w]
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    change c * c⁻¹ = 1
    exact mul_inv_cancel₀ hc.ne'
  let rel : A → V → Prop := fun v a => a ∈ A ∧ G.Adj v.val a
  let p := Real.exp (-k / (3 * n))
  have hp : 0 ≤ p := (Real.exp_pos _).le
  have hrow : ∀ v : A, ∑ a, w a * (if ¬rel v a then 1 else 0) ≤ p := by
    intro v
    let D := A.filter fun a => ¬G.Adj v.val a
    have hsum : (∑ a, w a * (if ¬rel v a then 1 else 0)) = (D.card : ℝ) / c := by
      calc
        _ = ∑ a : V, (if a ∈ A then c⁻¹ else 0) * (if a ∈ D then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : a ∈ A <;> by_cases hadj : G.Adj v.val a <;>
            simp [w, rel, D, ha, hadj]
        _ = ((A ∩ D).card : ℝ) * c⁻¹ := sum_uniform_mask A D _
        _ = (D.card : ℝ) / c := by
          rw [Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]; rfl
    have hcard : ((A.filter (G.Adj v.val)).card : ℝ) + (D.card : ℝ) = c := by
      dsimp [D, c]
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := A) (G.Adj v.val)
    have hdegree := hd v.val v.property
    have hcpos : 0 < 3 * n := by linarith
    have hquot : (D.card : ℝ) / c ≤ 1 - k / (3 * n) := by
      apply (div_le_iff₀ hc).mpr
      have hkn : k / (3 * n) * c ≤ k / 3 := by
        calc
          _ ≤ k / (3 * n) * n := mul_le_mul_of_nonneg_left hcn (by positivity)
          _ = k / 3 := by field_simp
      nlinarith
    rw [hsum]
    exact hquot.trans (by simpa [p, neg_div] using Real.one_sub_le_exp_neg (k / (3 * n)))
  have hlog : 0 < Real.log (2 * n) := Real.log_pos (by linarith)
  have hsreal : 10 * (n / k) * Real.log (2 * n) ≤ (s : ℝ) := Nat.le_ceil _
  have hexponent : (s : ℝ) * (k / (3 * n)) ≥ Real.log (2 * n) := by
    have hh := mul_le_mul_of_nonneg_right hsreal (show 0 ≤ k by positivity)
    have heq : (10 * (n / k) * Real.log (2 * n)) * k = 10 * n * Real.log (2 * n) := by
      field_simp
    rw [heq] at hh
    have h3n : 0 < 3 * n := by linarith
    rw [← mul_div_assoc]
    apply (le_div_iff₀ h3n).mpr
    change Real.log (2 * n) * (3 * n) ≤ (s : ℝ) * k
    nlinarith
  have hsmall : (Fintype.card A : ℝ) * p ^ s < 1 := by
    have he : p ^ s ≤ (2 * n)⁻¹ := by
      dsimp [p]
      rw [← Real.exp_nat_mul]
      calc
        _ ≤ Real.exp (-Real.log (2 * n)) := by
          apply Real.exp_le_exp.mpr
          simp only [neg_div, mul_neg]
          linarith
        _ = (2 * n)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by linarith)]
    have hca : (Fintype.card A : ℝ) = c := by simp [c]
    rw [hca]
    calc
      c * p ^ s ≤ n * (2 * n)⁻¹ := mul_le_mul hcn he (pow_nonneg hp _) (by linarith)
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  obtain ⟨f, hf⟩ := finite_hitting s w hw hs rel p hp hrow hsmall
  let R := (Finset.univ.image f) ∩ A
  refine ⟨R, Finset.inter_subset_right, ?_, ?_⟩
  · exact (Finset.card_le_card Finset.inter_subset_left).trans
      ((Finset.card_image_le).trans (by simp [s]))
  · intro v hv
    obtain ⟨i, hiA, hiadj⟩ := hf ⟨v, hv⟩
    exact ⟨f i, Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hiA⟩,
      hiadj⟩

end ConnectivityTests

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger
open SimpleGraph

namespace Density
variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma darts_card_le (S : Finset V) : (darts G S).card ≤ S.card * (S.card - 1) := by
  calc
    (darts G S).card ≤ S.offDiag.card := Finset.card_le_card (by
      intro e he
      obtain ⟨hx,hy,ha⟩ := (mem_darts G).mp he
      exact Finset.mem_offDiag.mpr ⟨hx,hy,ha.ne⟩)
    _ = _ := by simp [Finset.offDiag_card, Nat.mul_sub_left_distrib]

lemma darts_separator {S A Z B : Finset V} (h : SeparatorSplit G S A Z B) :
    (darts G S).card ≤ (darts G (A ∪ Z)).card + (darts G (B ∪ Z)).card := by
  apply (Finset.card_le_card (show darts G S ⊆ darts G (A ∪ Z) ∪ darts G (B ∪ Z) from ?_)).trans
    (Finset.card_union_le _ _)
  intro e he
  obtain ⟨hx,hy,ha⟩ := (mem_darts G).mp he
  rw [← h.union_eq] at hx hy
  simp only [Finset.mem_union] at hx hy ⊢
  rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy
  · exact Or.inl ((mem_darts G).mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_left _ hy,ha⟩)
  · exact Or.inl ((mem_darts G).mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_right _ hy,ha⟩)
  · exact (h.anticomplete _ hx _ hy ha).elim
  · exact Or.inl ((mem_darts G).mpr ⟨Finset.mem_union_right _ hx,Finset.mem_union_left _ hy,ha⟩)
  · exact Or.inl ((mem_darts G).mpr ⟨Finset.mem_union_right _ hx,Finset.mem_union_right _ hy,ha⟩)
  · exact Or.inr ((mem_darts G).mpr ⟨Finset.mem_union_right _ hx,Finset.mem_union_left _ hy,ha⟩)
  · exact (h.anticomplete _ hy _ hx ha.symm).elim
  · exact Or.inr ((mem_darts G).mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_right _ hy,ha⟩)
  · exact Or.inr ((mem_darts G).mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_left _ hy,ha⟩)

theorem connectivity_of_density (S : Finset V) {k : ℕ} (hk : 1 ≤ k)
    (hedges : 4*k*S.card < (darts G S).card) :
    ∃ T ⊆ S, KConnectedOn G T k := by
  classical
  have hbound := darts_card_le G S
  have hpos : 0 < S.card := by
    by_contra hn
    have hz : S.card = 0 := by omega
    simp only [hz, Nat.zero_mul] at hbound hedges
    omega
  have hlarge : 2*k ≤ S.card := by
    have hh : S.card - 1 ≤ S.card := Nat.sub_le _ _
    nlinarith
  let good := S.powerset.filter (fun T => 2*k ≤ T.card ∧ 4*k*(T.card-k) < (darts G T).card)
  have hSgood : S ∈ good := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _),hlarge,?_⟩
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) hedges
  obtain ⟨H,hHg,hmin⟩ := Finset.exists_min_image good Finset.card ⟨S,hSgood⟩
  obtain ⟨hHS,hHsize,hHedges⟩ : H ⊆ S ∧ 2*k ≤ H.card ∧
      4*k*(H.card-k) < (darts G H).card := by
    simpa only [good,Finset.mem_filter,Finset.mem_powerset,and_assoc] using hHg
  have hminimal (T : Finset V) (hTH : T ⊆ H) (hTk : 2*k ≤ T.card)
      (hcard : T.card < H.card) : (darts G T).card ≤ 4*k*(T.card-k) := by
    by_contra hn
    have hgood : T ∈ good := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (hTH.trans hHS),hTk,by omega⟩
    have := hmin T hgood
    omega
  have hHsize' : 2*k < H.card := by
    have hb := darts_card_le G H
    have hsub : H.card - 1 ≤ H.card := Nat.sub_le _ _
    by_contra hn
    have heq : H.card = 2*k := by omega
    have heq' : H.card - k = k := by omega
    rw [heq'] at hHedges
    nlinarith
  have hdegree (v : V) (hv : v ∈ H) : 2*k < (neighbors G H v).card := by
    have heq := Finset.card_erase_add_one hv
    have hd := darts_erase G hv
    have hb := hminimal (H.erase v) (Finset.erase_subset _ _) (by omega) (by omega)
    have hs : H.card-k = (H.erase v).card-k+1 := by omega
    rw [hs] at hHedges
    nlinarith
  refine ⟨H,hHS,?_⟩
  by_contra hn
  obtain ⟨A,Z,B,hZ,hsep⟩ := exists_separator G H (by omega) hn
  have hsub₁ : A ∪ Z ⊆ H := by rw [← hsep.union_eq]; exact Finset.subset_union_left
  have hsub₂ : B ∪ Z ⊆ H := by
    intro v hv
    rw [← hsep.union_eq]
    rcases Finset.mem_union.mp hv with hb | hz
    · exact Finset.mem_union_right _ hb
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  have hcard₁ : (A ∪ Z).card < H.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub₁,?_⟩
    intro heq
    obtain ⟨v,hv⟩ := hsep.right_nonempty
    have hvH : v ∈ H := by rw [← hsep.union_eq]; exact Finset.mem_union_right _ hv
    rw [←heq] at hvH
    rcases Finset.mem_union.mp hvH with ha | hz
    · exact Finset.disjoint_left.mp hsep.left_right ha hv
    · exact Finset.disjoint_left.mp hsep.sep_right hz hv
  have hcard₂ : (B ∪ Z).card < H.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub₂,?_⟩
    intro heq
    obtain ⟨v,hv⟩ := hsep.left_nonempty
    have hvH : v ∈ H := hsub₁ (Finset.mem_union_left _ hv)
    rw [←heq] at hvH
    rcases Finset.mem_union.mp hvH with hb | hz
    · exact Finset.disjoint_left.mp hsep.left_right hv hb
    · exact Finset.disjoint_left.mp hsep.left_sep hv hz
  have hsize₁ : 2*k ≤ (A ∪ Z).card := by
    obtain ⟨v,hv⟩ := hsep.left_nonempty
    have hd := hdegree v (hsub₁ (Finset.mem_union_left _ hv))
    have hb : (neighbors G H v).card ≤ (A ∪ Z).card := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨hwH,ha⟩ := (mem_neighbors G).mp hw
      rw [←hsep.union_eq] at hwH
      rcases Finset.mem_union.mp hwH with hw | hw
      · exact hw
      · exact (hsep.anticomplete _ hv _ hw ha).elim
    omega
  have hsize₂ : 2*k ≤ (B ∪ Z).card := by
    obtain ⟨v,hv⟩ := hsep.right_nonempty
    have hd := hdegree v (hsub₂ (Finset.mem_union_left _ hv))
    have hb : (neighbors G H v).card ≤ (B ∪ Z).card := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨hwH,ha⟩ := (mem_neighbors G).mp hw
      rw [←hsep.union_eq] at hwH
      rcases Finset.mem_union.mp hwH with hw | hw
      · rcases Finset.mem_union.mp hw with hw | hw
        · exact (hsep.anticomplete _ hw _ hv ha.symm).elim
        · exact Finset.mem_union_right _ hw
      · exact Finset.mem_union_left _ hw
    omega
  have hb₁ := hminimal (A ∪ Z) hsub₁ hsize₁ hcard₁
  have hb₂ := hminimal (B ∪ Z) hsub₂ hsize₂ hcard₂
  have hedge := darts_separator G hsep
  have hcards : (A ∪ Z).card + (B ∪ Z).card = H.card + Z.card := by
    rw [Finset.card_union_of_disjoint hsep.left_sep,
      Finset.card_union_of_disjoint hsep.sep_right.symm, ← hsep.union_eq,
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
        ⟨hsep.left_right,hsep.sep_right⟩),Finset.card_union_of_disjoint hsep.left_sep]
    omega
  have h1 : (A ∪ Z).card-k+k = (A ∪ Z).card := Nat.sub_add_cancel (by omega)
  have h2 : (B ∪ Z).card-k+k = (B ∪ Z).card := Nat.sub_add_cancel (by omega)
  have hH : H.card-k+k = H.card := Nat.sub_add_cancel (by omega)
  nlinarith

theorem edge_density_connectivity [Fintype V] {k : ℕ} (hk : 1 ≤ k)
    (he : 2*k*Fintype.card V < G.edgeFinset.card) :
    ∃ T : Finset V, KConnectedOn G T k := by
  obtain ⟨T,_,hT⟩ := connectivity_of_density G Finset.univ hk (by
    rw [darts_univ,Finset.card_univ]
    nlinarith)
  exact ⟨T,hT⟩

end Density

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Fractional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Fractional
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

lemma cost_nonneg {G : SimpleGraph V} {μ : Finset V → ℝ} (h : Cover G μ) : 0 ≤ cost μ :=
  Finset.sum_nonneg (fun I _ => h.1 I)

lemma singletonWeights_cover (G : SimpleGraph V) : Cover G singletonWeights := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro I
    exact Finset.sum_nonneg fun v _ => by split_ifs <;> norm_num
  · intro I hn
    apply Finset.sum_eq_zero
    intro v _
    rw [ite_eq_right]
    rintro rfl
    exact hn (stable_singleton G v)
  · intro v
    have hpos (I : Finset V) : 0 ≤ (if v ∈ I then singletonWeights I else 0) := by
      split_ifs
      · exact Finset.sum_nonneg fun w _ => by split_ifs <;> norm_num
      · exact le_rfl
    have h := Finset.single_le_sum (fun I _ => hpos I) (Finset.mem_univ ({v} : Finset V))
    have hm : singletonWeights ({v} : Finset V) = 1 := by
      simp [singletonWeights,Finset.singleton_inj]
    simpa [hm] using h

lemma costs_nonempty (G : SimpleGraph V) :
    ({c : ℝ | ∃ μ, Cover G μ ∧ cost μ = c} : Set ℝ).Nonempty :=
  ⟨_,singletonWeights,singletonWeights_cover G,rfl⟩

lemma costs_bddBelow (G : SimpleGraph V) :
    BddBelow {c : ℝ | ∃ μ, Cover G μ ∧ cost μ = c} := by
  refine ⟨0,?_⟩
  rintro c ⟨μ,hμ,rfl⟩
  exact cost_nonneg hμ

lemma number_le_cost {G : SimpleGraph V} {μ : Finset V → ℝ} (h : Cover G μ) :
    number G ≤ cost μ := csInf_le (costs_bddBelow G) ⟨μ,h,rfl⟩

lemma Cover.clamp {G : SimpleGraph V} {μ : Finset V → ℝ} (h : Cover G μ) :
    Cover G (fun I => min (μ I) 1) := by
  classical
  refine ⟨fun I => le_min (h.1 I) zero_le_one,?_,?_⟩
  · intro I hn
    change min (μ I) 1 = 0
    rw [h.2.1 I hn]
    norm_num
  · intro v
    by_cases hall : ∀ I, v ∈ I → μ I ≤ 1
    · have heq : (∑ I, if v ∈ I then min (μ I) 1 else 0) =
          ∑ I, if v ∈ I then μ I else 0 := by
        apply Finset.sum_congr rfl
        intro I _
        split_ifs with hv
        · rw [min_eq_left (hall I hv)]
        · rfl
      rw [heq]
      exact h.2.2 v
    · push Not at hall
      obtain ⟨I,hv,hI⟩ := hall
      have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Finset V)))
        (f := fun J => if v ∈ J then min (μ J) 1 else 0)
        (fun J _ => by split_ifs; exact le_min (h.1 J) zero_le_one; exact le_rfl)
        (Finset.mem_univ I)
      simpa only [ite_eq_left hv,min_eq_right (le_of_lt hI)] using hs

lemma cover_isClosed (G : SimpleGraph V) : IsClosed {μ : Finset V → ℝ | Cover G μ} := by
  change IsClosed ({μ : Finset V → ℝ | ∀ I, 0 ≤ μ I} ∩
    ({μ | ∀ I, ¬Stable G I → μ I = 0} ∩
     {μ | ∀ v, 1 ≤ ∑ I, if v ∈ I then μ I else 0}))
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun I => isClosed_le continuous_const (continuous_apply I)
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro I
    by_cases h : Stable G I
    · simp only [h,not_true_eq_false,false_implies,Set.ofPred_true]
      exact isClosed_univ
    · simp only [h,not_false_eq_true,true_implies]
      exact isClosed_eq (continuous_apply I) continuous_const
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    apply continuous_finsetSum
    intro I _
    by_cases hv : v ∈ I
    · simpa only [ite_eq_left hv] using continuous_apply I
    · simp only [ite_eq_right hv]
      exact continuous_const

lemma cost_continuous {V : Type} [Fintype V] [DecidableEq V] : Continuous (cost (V := V)) := by
  apply continuous_finsetSum
  intro I _
  exact continuous_apply I

theorem optimum_exists (G : SimpleGraph V) : ∃ μ, Cover G μ ∧ cost μ = number G := by
  classical
  let K : Set ((Finset V) → ℝ) := Set.Icc 0 1 ∩ {μ | Cover G μ}
  have hcomp : IsCompact K := isCompact_Icc.inter_right (cover_isClosed G)
  have hne : K.Nonempty := by
    refine ⟨fun I => min (singletonWeights I) 1,⟨?_,?_⟩,(singletonWeights_cover G).clamp⟩
    · intro I
      exact le_min ((singletonWeights_cover G).1 I) zero_le_one
    · intro I
      exact min_le_right _ _
  obtain ⟨μ,hμ,hmin⟩ := hcomp.exists_isMinOn hne cost_continuous.continuousOn
  refine ⟨μ,hμ.2,le_antisymm ?_ (number_le_cost hμ.2)⟩
  apply le_csInf (costs_nonempty G)
  rintro c ⟨ν,hν,rfl⟩
  apply (hmin (show (fun I => min (ν I) 1) ∈ K from ?_)).trans
    (Finset.sum_le_sum (fun I _ => min_le_left (ν I) 1))
  exact ⟨⟨fun I => le_min (hν.1 I) zero_le_one,fun I => min_le_right _ _⟩,hν.clamp⟩

lemma transport_expect {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : α → ℝ) (f : α → β) (X : β → ℝ) :
    (∑ b, transport μ f b * X b) = ∑ a, μ a * X (f a) := by
  classical
  simp only [transport,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul,zero_mul]
  simp

lemma transport_sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : α → ℝ) (f : α → β) : ∑ b, transport μ f b = ∑ a, μ a := by
  simpa only [mul_one] using transport_expect μ f (fun _ => 1)

lemma transport_nonneg {α β : Type} [Fintype α] [DecidableEq β]
    {μ : α → ℝ} (hμ : ∀ a, 0 ≤ μ a) (f : α → β) (b : β) : 0 ≤ transport μ f b := by
  exact Finset.sum_nonneg fun a _ => by split_ifs; exact hμ a; exact le_rfl

lemma marginal_eq_expect (μ : Finset V → ℝ) (v : V) :
    marginal μ v = ∑ I, μ I * indicator I v := by
  classical
  simp [marginal,indicator,mul_ite]

lemma cover_comap {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {μ : Finset V → ℝ} (hμ : Cover G μ) (f : W → V) :
    ∃ ν, Cover (G.comap f) ν ∧ cost ν = cost μ := by
  classical
  let pull : Finset V → Finset W := fun I => Finset.univ.filter (fun w => f w ∈ I)
  let ν := transport μ pull
  have hstable (I : Finset V) (hI : Stable G I) : Stable (G.comap f) (pull I) := by
    intro u hu v hv hadj
    exact hI (f u) (Finset.mem_filter.mp hu).2 (f v) (Finset.mem_filter.mp hv).2 hadj
  refine ⟨ν,⟨transport_nonneg hμ.1 pull,?_,?_⟩,transport_sum μ pull⟩
  · intro J hn
    apply Finset.sum_eq_zero
    intro I _
    split_ifs with he
    · apply hμ.2.1 I
      intro hI
      apply hn
      rw [← he]
      exact hstable I hI
    · rfl
  · intro w
    change 1 ≤ marginal ν w
    rw [marginal_eq_expect,transport_expect]
    have he (I : Finset V) : indicator (pull I) w = indicator I (f w) := by
      simp [indicator,pull]
    simp only [he,← marginal_eq_expect]
    exact hμ.2.2 (f w)

lemma number_comap {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (f : W → V) : number (G.comap f) ≤ number G := by
  obtain ⟨μ,hμ,heq⟩ := optimum_exists G
  obtain ⟨ν,hν,hcost⟩ := cover_comap hμ f
  exact (number_le_cost hν).trans_eq (hcost.trans heq)

end LinearListHadwiger.Fractional

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Knitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Knitting
open SimpleGraph PathPacking
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem short_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) {k : ℕ} (hk : 0 < k)
    (hdeg : ∀ v, k ≤ (Density.neighbors G Finset.univ v).card) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length < 3 * (Fintype.card V / k + 1) := by
  classical
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
  let n := p.length / 3 + 1
  let N (i : Fin n) := Density.neighbors G Finset.univ (p.getVert (3*i.val))
  have hidx : ∀ i : Fin n, 3*i.val ≤ p.length := by
    intro i
    have := i.isLt
    dsimp [n] at this
    have := Nat.mod_add_div p.length 3
    omega
  have hdist : ∀ i : Fin n, G.dist u (p.getVert (3*i.val)) = 3*i.val := by
    intro i
    have h := length_eq_dist_of_subwalk hp (p.isSubwalk_take (3*i.val))
    simpa [Walk.take_length, Nat.min_eq_left (hidx i)] using h.symm
  have hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (N i) (N j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    have hi : G.Adj (p.getVert (3*i.val)) w := (Density.mem_neighbors G).mp hwi |>.2
    have hj : G.Adj (p.getVert (3*j.val)) w := (Density.mem_neighbors G).mp hwj |>.2
    have h₁ := hc.dist_triangle (u := u) (v := p.getVert (3*i.val)) (w := w)
    have h₂ := hc.dist_triangle (u := u) (v := w) (w := p.getVert (3*j.val))
    have h₃ := hc.dist_triangle (u := u) (v := p.getVert (3*j.val)) (w := w)
    have h₄ := hc.dist_triangle (u := u) (v := w) (w := p.getVert (3*i.val))
    rw [hdist i, dist_eq_one_iff_adj.mpr hi] at h₁
    rw [hdist j, dist_eq_one_iff_adj.mpr hj.symm] at h₂
    rw [hdist j, dist_eq_one_iff_adj.mpr hj] at h₃
    rw [hdist i, dist_eq_one_iff_adj.mpr hi.symm] at h₄
    have he : i.val = j.val := by omega
    exact hij (Fin.ext he)
  have hsum : (∑ i : Fin n, (N i).card) ≤ Fintype.card V := by
    rw [← Finset.card_biUnion (s := Finset.univ) (t := N)]
    · exact Finset.card_le_univ _
    · intro i _ j _ hij
      exact hdisj i j hij
  have hnk : n*k ≤ Fintype.card V := by
    calc
      n*k = ∑ i : Fin n, k := by simp
      _ ≤ ∑ i : Fin n, (N i).card := Finset.sum_le_sum (fun i _ => hdeg _)
      _ ≤ Fintype.card V := hsum
  have hn : n ≤ Fintype.card V / k := (Nat.le_div_iff_mul_le hk).mpr hnk
  refine ⟨p,p.isPath_of_length_eq_dist hp,?_⟩
  have := Nat.mod_lt p.length (by omega : 0 < 3)
  have := Nat.mod_add_div p.length 3
  dsimp [n] at hn
  omega

lemma min_degree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {k : ℕ} (hc : KConnectedOn G S k) {u : V} (hu : u ∈ S) :
    k ≤ (Density.neighbors G S u).card := by
  classical
  by_contra hn
  have hn : (Density.neighbors G S u).card < k := by omega
  let N := Density.neighbors G S u
  have hNS : N ⊆ S := Finset.filter_subset _ _
  have huN : u ∉ N := by simp [N,Density.neighbors]
  have huR : u ∈ S \ N := Finset.mem_sdiff.mpr ⟨hu,huN⟩
  have hnot : ¬S \ N ⊆ {u} := by
    intro h
    have hh := Finset.card_le_card h
    have he := Finset.card_sdiff_add_card_eq_card hNS
    have hs := hc.1
    simp only [Finset.card_singleton] at hh
    dsimp [N] at he hh
    omega
  simp only [Finset.subset_iff,not_forall,Finset.mem_singleton] at hnot
  obtain ⟨v,hv,hvu⟩ := hnot
  obtain ⟨p⟩ := (hc.2 N hNS hn).preconnected ⟨u,huR⟩ ⟨v,hv⟩
  have hp : ¬p.Nil := p.not_nil_of_ne (fun h => hvu (congrArg Subtype.val h).symm)
  have ha : G.Adj u p.snd.val := p.adj_snd hp
  exact (Finset.mem_sdiff.mp p.snd.property).2
    (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp p.snd.property).1,ha⟩)

lemma induce_connected {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) {k : ℕ}
    (hc : KConnectedOn G S k) :
    KConnectedOn (G.induce (↑S : Set V)) Finset.univ k := by
  classical
  refine ⟨by simpa using hc.1,?_⟩
  intro X _ hx
  let Z := X.image Subtype.val
  have hZ : Z ⊆ S := by
    intro v hv
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  have hZk : Z.card < k := by simpa [Z,Finset.card_image_of_injective _ Subtype.val_injective] using hx
  have hconn := hc.2 Z hZ hZk
  let f : G.induce (↑(S \ Z) : Set V) →g
      (G.induce (↑S : Set V)).induce (↑(Finset.univ \ X) : Set ↥S) :=
    { toFun := fun v => ⟨⟨v.val,(Finset.mem_sdiff.mp v.property).1⟩,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hv =>
          (Finset.mem_sdiff.mp v.property).2 (Finset.mem_image.mpr ⟨_,hv,rfl⟩)⟩⟩
      map_rel' := by intro u v h; exact h }
  apply hconn.map f
  intro w
  have hw : w.val.val ∈ S \ Z := by
    refine Finset.mem_sdiff.mpr ⟨w.val.property,?_⟩
    intro hz
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hz
    have heq : a = w.val := Subtype.ext he
    exact (Finset.mem_sdiff.mp w.property).2 (heq ▸ ha)
  exact ⟨⟨w.val.val,hw⟩,rfl⟩

end LinearListHadwiger.Knitting

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.TerminalGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Knitting
open SimpleGraph PathPacking
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma model_card_le {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (M : MinorModel G H) : Fintype.card W ≤ Fintype.card V := by
  classical
  let f (w : W) : V := (M.connected w).nonempty.some.val
  have hf : ∀ w, f w ∈ M.branch w := fun w => (M.connected w).nonempty.some.property
  apply Fintype.card_le_of_injective f
  intro a b he
  by_contra hn
  exact Set.disjoint_left.mp (M.disjoint a b hn) (hf a) (he ▸ hf b)

lemma density_iso {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : density G = density H := by
  unfold density
  rw [e.card_edgeFinset_eq, e.card_eq]

theorem maximal_minor_density (G : SimpleGraph V) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)), Nonempty (MinorModel G H) ∧
      ∀ (W : Type) [Fintype W] [DecidableEq W] (J : SimpleGraph W),
        Nonempty (MinorModel G J) → density J ≤ density H := by
  classical
  let Family := Σ n : Fin (Fintype.card V + 1), SimpleGraph (Fin n.val)
  let candidates : Finset Family := Finset.univ.filter fun p => Nonempty (MinorModel G p.2)
  have hnon : candidates.Nonempty := by
    let p : Family := ⟨⟨Fintype.card V,by omega⟩,G.overFin rfl⟩
    refine ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    exact ⟨model_relabel (model_singletons G) (G.overFinIso rfl)⟩
  obtain ⟨p,hp,hmax⟩ := candidates.exists_max_image (fun p => density p.2) hnon
  refine ⟨p.1.val,p.2,(Finset.mem_filter.mp hp).2,?_⟩
  intro W _ _ J hJ
  obtain ⟨M⟩ := hJ
  let q : Family := ⟨⟨Fintype.card W,by have := model_card_le M; omega⟩,J.overFin rfl⟩
  have hq : q ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ⟨model_relabel M (J.overFinIso rfl)⟩⟩
  have hh := hmax q hq
  exact (density_iso (J.overFinIso rfl)).le.trans hh

private lemma proj_collision {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v a b c d : V}
    (huv : u≠v) (ha : edgeGood G u v a b) (hc : edgeGood G u v c d)
    (hac : proj u v huv a = proj u v huv c)
    (hbd : proj u v huv b = proj u v huv d) : a=c := by
  have hcval := congrArg Subtype.val hac
  have hdval := congrArg Subtype.val hbd
  dsimp [proj] at hcval hdval
  by_cases hav : a=v
  · by_cases hcv : c=v
    · exact hav.trans hcv.symm
    · have hcu : c=u := by simpa [hav,hcv] using hcval.symm
      have hp := ha.2.1 hav
      have hb : b≠v := by intro he; exact ha.1.ne (hav.trans he.symm)
      have hd : d≠v := by
        intro he
        exact hp.1 (by simpa [he,hb] using hdval)
      have hbe : b=d := by simpa [hb,hd] using hdval
      exact (hp.2 (hcu ▸ hbe.symm ▸ hc.1)).elim
  · by_cases hcv : c=v
    · have hau : a=u := by simpa [hav,hcv] using hcval
      have hp := hc.2.1 hcv
      have hd : d≠v := by intro he; exact hc.1.ne (hcv.trans he.symm)
      have hb : b≠v := by
        intro he
        exact hp.1 (by simpa [he,hd] using hdval.symm)
      have hbe : b=d := by simpa [hb,hd] using hdval
      exact (hp.2 (hau ▸ hbe ▸ ha.1)).elim
    · simpa [hav,hcv] using hcval

private lemma proj_adj {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v a b : V} (huv : u≠v)
    (ha : edgeGood G u v a b) :
    (contractEdge G u v).Adj (proj u v huv a) (proj u v huv b) := by
  refine ⟨?_,?_⟩
  · intro he
    have hv := congrArg Subtype.val he
    dsimp [proj] at hv
    by_cases hav : a=v <;> by_cases hbv : b=v
    · exact ha.1.ne (hav.trans hbv.symm)
    · exact (ha.2.1 hav).1 (by simpa [hav,hbv] using hv.symm)
    · exact (ha.2.2 hbv).1 (by simpa [hav,hbv] using hv)
    · exact ha.1.ne (by simpa [hav,hbv] using hv)
  · by_cases hav : a=v <;> by_cases hbv : b=v
    · exact (ha.1.ne (hav.trans hbv.symm)).elim
    · right; left
      exact ⟨by simp [proj,hav], by simpa [proj,hbv,hav] using ha.1⟩
    · right; right
      exact ⟨by simp [proj,hbv], by simpa [proj,hbv,hav] using ha.1.symm⟩
    · left
      simpa [proj,hav,hbv] using ha.1

theorem contract_edge_count (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    G.edgeFinset.card ≤ (contractEdge G u v).edgeFinset.card + 1 + (common G u v).card := by
  classical
  let D := Density.darts G Finset.univ
  let good := D.filter fun z => edgeGood G u v z.1 z.2
  let bad := D \ good
  let N := insert u (common G u v)
  have hN : N.card ≤ 1+(common G u v).card := by
    exact (Finset.card_insert_le _ _).trans (by omega)
  have hbad : bad ⊆ N.image (fun w => (v,w)) ∪ N.image (fun w => (w,v)) := by
    intro z hz
    have hzD := (Finset.mem_sdiff.mp hz).1
    have hzG : G.Adj z.1 z.2 := (Finset.mem_filter.mp hzD).2
    have hng : ¬edgeGood G u v z.1 z.2 := by
      intro hg
      exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_filter.mpr ⟨hzD,hg⟩)
    by_cases hfst : z.1=v
    · by_cases hleft : z.2≠u ∧ ¬G.Adj u z.2
      · have hright : z.2=v → z.1≠u ∧ ¬G.Adj u z.1 := by
          intro he; exact (hzG.ne (hfst.trans he.symm)).elim
        exact (hng ⟨hzG,fun _ => hleft,hright⟩).elim
      · have hmem : z.2 ∈ N := by
          dsimp [N]
          by_cases hzu : z.2=u
          · exact Finset.mem_insert.mpr (Or.inl hzu)
          · have had : G.Adj u z.2 := by tauto
            exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _,had,hfst ▸ hzG⟩))
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z.2,hmem,Prod.ext hfst.symm rfl⟩)
    · have hsnd : z.2=v := by
        by_contra hn
        exact hng ⟨hzG,fun he => (hfst he).elim,fun he => (hn he).elim⟩
      have hright : ¬(z.1≠u ∧ ¬G.Adj u z.1) := by
        intro hr; exact hng ⟨hzG,fun he => (hfst he).elim,fun _ => hr⟩
      have hmem : z.1 ∈ N := by
        dsimp [N]
        by_cases hzu : z.1=u
        · exact Finset.mem_insert.mpr (Or.inl hzu)
        · have had : G.Adj u z.1 := by tauto
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _,had,hsnd ▸ hzG.symm⟩))
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z.1,hmem,Prod.ext rfl hsnd.symm⟩)
  have hbadcard : bad.card ≤ 2*(1+(common G u v).card) := by
    have hb := (Finset.card_le_card hbad).trans (Finset.card_union_le _ _)
    have h₁ := Finset.card_image_le (s := N) (f := fun w => (v,w))
    have h₂ := Finset.card_image_le (s := N) (f := fun w => (w,v))
    omega
  let f (z : V×V) := (proj u v huv.ne z.1,proj u v huv.ne z.2)
  have hf : Set.InjOn f (↑good : Set (V×V)) := by
    intro a ha b hb he
    have hag := (Finset.mem_filter.mp ha).2
    have hbg := (Finset.mem_filter.mp hb).2
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    refine Prod.ext (proj_collision huv.ne hag hbg hfst hsnd) ?_
    exact proj_collision huv.ne ⟨hag.1.symm,hag.2.2,hag.2.1⟩
      ⟨hbg.1.symm,hbg.2.2,hbg.2.1⟩ hsnd hfst
  have hfD : good.image f ⊆ Density.darts (contractEdge G u v) Finset.univ := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨by simp,proj_adj huv.ne (Finset.mem_filter.mp ha).2⟩
  have hgcard : good.card ≤ (Density.darts (contractEdge G u v) Finset.univ).card := by
    rw [← Finset.card_image_of_injOn hf]
    exact Finset.card_le_card hfD
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun z => edgeGood G u v z.1 z.2) D)
  change bad.card + good.card = D.card at hsum
  have hD : D.card = 2*G.edgeFinset.card := Density.darts_univ G
  rw [Density.darts_univ] at hgcard
  omega

lemma density_mul_order {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hn : 0 < Fintype.card V) :
    density G * Fintype.card V = (G.edgeFinset.card : ℚ) := by
  unfold density
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

lemma degree_le_twice_density (G : SimpleGraph V) (hn : 0 < Fintype.card V) :
    ∃ u, (G.degree u : ℚ) ≤ 2*density G := by
  classical
  by_contra! h
  have hab := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    (f := fun _ : V => 2*density G) (g := fun v => (G.degree v : ℚ))
    (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn)) (fun v _ => h v)
  have hsum : (∑ v, (G.degree v : ℚ)) = 2*(G.edgeFinset.card : ℚ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hab
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hab
  have he := density_mul_order G hn
  nlinarith

lemma common_of_max_density (G : SimpleGraph V) (hmax : ∀ (W : Type) [Fintype W]
    [DecidableEq W] (J : SimpleGraph W), Nonempty (MinorModel G J) → density J ≤ density G)
    {u v : V} (huv : G.Adj u v) : density G ≤ 1+(common G u v).card := by
  classical
  let H := contractEdge G u v
  have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨u,v,huv.ne⟩
  have hn' : Fintype.card {w : V // w ≠ v} = Fintype.card V - 1 := by
    simp
  have hh : 0 < Fintype.card {w : V // w≠v} := by omega
  have heH := density_mul_order H hh
  have heG := density_mul_order G (by omega)
  have hcount : (G.edgeFinset.card : ℚ) ≤ (H.edgeFinset.card : ℚ)+1+(common G u v).card :=
    by exact_mod_cast contract_edge_count G huv
  have hle := hmax _ H ⟨contract_model G huv⟩
  have hmul := mul_le_mul_of_nonneg_right hle (show (0 : ℚ) ≤ Fintype.card {w : V // w≠v} by positivity)
  rw [heH,hn',Nat.cast_sub (by omega : 1 ≤ Fintype.card V)] at hmul
  norm_num only [Nat.cast_one] at hmul
  nlinarith

lemma neighborhood_degree (G : SimpleGraph V) (u : V) (v : ↥(G.neighborFinset u)) :
    ((G.induce (↑(G.neighborFinset u) : Set V)).degree v) = (common G u v.val).card := by
  classical
  have he : ((G.induce (↑(G.neighborFinset u) : Set V)).neighborFinset v).image Subtype.val =
      common G u v.val := by
    ext w
    simp only [Finset.mem_image,SimpleGraph.mem_neighborFinset,SimpleGraph.induce_adj,
      common,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(SimpleGraph.mem_neighborFinset _ _ _).mp z.property,hz⟩
    · rintro ⟨hw,hv⟩
      exact ⟨⟨w,(SimpleGraph.mem_neighborFinset _ _ _).mpr hw⟩,hv,rfl⟩
  rw [← he,Finset.card_image_of_injective _ Subtype.val_injective,
    SimpleGraph.card_neighborFinset_eq_degree]

lemma kConnected_iso {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) {k : ℕ}
    (hc : KConnectedOn G Finset.univ k) : KConnectedOn H Finset.univ k := by
  classical
  refine ⟨?_,?_⟩
  · simpa only [Finset.card_univ,← e.card_eq] using hc.1
  · intro X _ hX
    let Z := X.image e.symm
    have hZ : Z.card < k := by simpa [Z,Finset.card_image_of_injective _ e.symm.injective] using hX
    have hconn := hc.2 Z (Finset.subset_univ _) hZ
    let f : (G.induce (↑(Finset.univ \ Z) : Set V)) →g
        (H.induce (↑(Finset.univ \ X) : Set W)) :=
      { toFun := fun v => ⟨e v.val,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hv =>
          (Finset.mem_sdiff.mp v.property).2
            (Finset.mem_image.mpr ⟨e v.val,hv,e.symm_apply_apply v.val⟩)⟩⟩
        map_rel' := by intro u v h; exact e.map_rel_iff.mpr h }
    apply hconn.map f
    intro w
    have hw : e.symm w.val ∈ Finset.univ \ Z := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
      intro hz
      obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_sdiff.mp w.property).2 (e.symm.injective he ▸ ha)
    exact ⟨⟨e.symm w.val,hw⟩,Subtype.ext (e.apply_symm_apply w.val)⟩

theorem small_minor_core (G : SimpleGraph V) (hlower : (16 : ℚ) ≤ density G) :
    ∃ (n k : ℕ) (H : SimpleGraph (Fin n)), Nonempty (MinorModel G H) ∧
      KConnectedOn H Finset.univ k ∧ n ≤ 32*k ∧
      density G < 8*(k+1) := by
  classical
  obtain ⟨q,J,⟨M⟩,hmax⟩ := maximal_minor_density G
  have hdiag := hmax V G ⟨model_singletons G⟩
  have hd : (16 : ℚ) ≤ density J := hlower.trans hdiag
  have hJmax : ∀ (W : Type) [Fintype W] [DecidableEq W] (L : SimpleGraph W),
      Nonempty (MinorModel J L) → density L ≤ density J := by
    intro W _ _ L hL
    obtain ⟨N⟩ := hL
    exact hmax W L ⟨compose_model M N⟩
  have hJ : 0 < Fintype.card (Fin q) := by
    by_contra hn
    have hh : Fintype.card (Fin q)=0 := by omega
    norm_num [density,hh] at hd
  let k := ⌊density J / 8⌋₊
  have hk : 2 ≤ k := Nat.le_floor (by linarith : (2 : ℚ) ≤ density J/8)
  have hklo : (8*k : ℚ) ≤ density J := by
    have hh := Nat.floor_le (by linarith : (0 : ℚ) ≤ density J/8)
    change (k : ℚ) ≤ density J/8 at hh
    linarith
  have hkhi : density J < 8*((k : ℚ)+1) := by
    have hh := Nat.lt_floor_add_one (density J/8)
    change density J/8 < (k : ℚ)+1 at hh
    linarith
  obtain ⟨u,hu⟩ := degree_le_twice_density J hJ
  let S := J.neighborFinset u
  let : Fintype (↑S : Set (Fin q)) := inferInstanceAs (Fintype ↥S)
  let L := J.induce (↑S : Set (Fin q))
  have hS : (S.card : ℚ) ≤ 2*density J := by simpa [S] using hu
  have hdeg : ∀ v : ↥S, (8*k : ℚ)-1 ≤ L.degree v := by
    intro v
    have hv := common_of_max_density J hJmax ((SimpleGraph.mem_neighborFinset _ _ _).mp v.property)
    rw [← neighborhood_degree J u v] at hv
    linarith
  have hSpos : 0 < S.card := by
    by_contra hn
    have he : S.card=0 := by omega
    have hdu : J.degree u=0 := by simpa [S] using he

    let T : Finset (Fin q) := Finset.univ.erase u
    let : Fintype (↑T : Set (Fin q)) := inferInstanceAs (Fintype ↥T)
    let P := J.induce (↑T : Set (Fin q))
    have hT : T.card+1=q := by
      have := Finset.card_erase_add_one (Finset.mem_univ u)
      simpa [T] using this
    have hed : P.edgeFinset.card = J.edgeFinset.card := by
      have hs : (↑T : Set (Fin q)) = {u}ᶜ := by ext w; simp [T]
      dsimp [P]
      have hh := SimpleGraph.card_edgeFinset_induce_compl_singleton J u
      rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet,hdu,Nat.sub_zero] at hh
      let e : P ≃g (J.induce {u}ᶜ) :=
        { toEquiv := Equiv.setCongr hs
          map_rel_iff' := by intro a b; rfl }
      exact e.card_edgeFinset_eq.trans hh
    have hql : 1 < q := by
      by_contra hn
      have hqpos : 0<q := by simpa using hJ
      have hq : q=1 := by omega
      have hc : J.edgeFinset.card=0 := by
        have hh := SimpleGraph.card_edgeFinset_le_card_choose_two (G := J)
        simp only [Fintype.card_fin,hq] at hh
        norm_num at hh
        simp [hh]
      norm_num [density,hc] at hd
    have htpos : 0 < Fintype.card ↥T := by simpa using (show 0<T.card by omega)
    have hPmax := hJmax _ P ⟨model_induce J T⟩
    have heP := density_mul_order P htpos
    have heJ := density_mul_order J hJ
    erw [hed] at heP
    have htc : (Fintype.card ↥T : ℚ)+1 = Fintype.card (Fin q) := by
      exact_mod_cast (by simpa using hT : Fintype.card ↥T+1=Fintype.card (Fin q))
    have hm := mul_le_mul_of_nonneg_right hPmax (show (0 : ℚ) ≤ Fintype.card ↥T by positivity)
    have heP' : density P * (T.card : ℚ) = (J.edgeFinset.card : ℚ) := by
      have hh : Fintype.card (↑T : Set (Fin q)) = T.card := Fintype.card_coe T
      erw [hh] at heP
      exact heP
    have hm' : density P * (T.card : ℚ) ≤ density J * (T.card : ℚ) := by
      simpa only [Fintype.card_coe] using hm
    have htc' : (T.card : ℚ)+1 = Fintype.card (Fin q) := by simpa only [Fintype.card_coe] using htc
    nlinarith [heP',hm',htc']
  have hedge : 2*k*Fintype.card ↥S < L.edgeFinset.card := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hdeg v)
    have hsum : (∑ v, (L.degree v : ℚ)) = 2*(L.edgeFinset.card : ℚ) := by
      exact_mod_cast L.sum_degrees_eq_twice_card_edges
    erw [hsum] at hs
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
    have hn : (0 : ℚ) < Fintype.card ↥S := by exact_mod_cast (by simpa using hSpos : 0<Fintype.card ↥S)
    have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
    have hh : (2*k*Fintype.card ↥S : ℚ)<L.edgeFinset.card := by nlinarith
    exact_mod_cast hh
  obtain ⟨T,hTc⟩ := Density.edge_density_connectivity L (by omega) hedge
  let : Fintype (↑T : Set ↥S) := inferInstanceAs (Fintype ↥T)
  let H := L.induce (↑T : Set ↥S)
  have hHc := induce_connected L T hTc
  let N := compose_model M (compose_model (model_induce J S) (model_induce L T))
  let e := H.overFinIso rfl
  refine ⟨Fintype.card ↥T,k,H.overFin rfl,⟨model_relabel N e⟩,?_,?_,?_⟩
  ·
    exact kConnected_iso e hHc
  · have ht : T.card ≤ S.card := by simpa using Finset.card_le_univ T
    have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
    have hh : (S.card : ℚ) ≤ 32*k := by nlinarith
    exact (by simpa using ht : Fintype.card ↥T ≤ S.card).trans (by exact_mod_cast hh)
  · exact hdiag.trans_lt hkhi

end LinearListHadwiger.Knitting

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.CoarseDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.CoarseDensity
open SimpleGraph Finset
open Knitting
variable {V : Type} [Fintype V] [DecidableEq V]

theorem connected_dominating (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) {N k : ℕ} (hk : 0 < k)
    (hn : Fintype.card V ≤ N)
    (hd : ∀ v, k ≤ (Density.neighbors G univ v).card) :
    ∃ D : Finset V, (G.induce (↑D : Set V)).Connected ∧
      (∀ v, ∃ w ∈ D, G.Adj v w) ∧
      D.card ≤ 3*(N/k+1)*⌈10*((N:ℝ)/(3*k))*Real.log (2*N)⌉₊ := by
  classical
  have : Nonempty V := hc.nonempty
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast ((Nat.succ_le_iff.mpr Fintype.card_pos).trans hn)
  obtain ⟨R,_,hR,hcover⟩ := ConnectivityTests.exists_neighborhood_cover G univ hN
    (by positivity : (0:ℝ)<3*k) (by simp)
    (by exact_mod_cast hn) (fun v _ => by
      simpa only [mul_div_cancel_left₀ (k:ℝ) (by norm_num : (3:ℝ)≠0)] using
        (show (k:ℝ) ≤ ((univ.filter (G.Adj v)).card:ℝ) by exact_mod_cast hd v))
  have hRn : R.Nonempty := by
    obtain ⟨w,hw,_⟩ := hcover (Classical.arbitrary V) (mem_univ _)
    exact ⟨w,hw⟩
  obtain ⟨r,hr⟩ := hRn
  have hp : ∀ v : R, ∃ p : G.Walk r v.val, p.IsPath ∧ p.length < 3*(N/k+1) := by
    intro v
    obtain ⟨p,hp,hl⟩ := short_path G hc hk hd r v.val
    exact ⟨p,hp,hl.trans_le (Nat.mul_le_mul_left 3 (Nat.add_le_add_right (Nat.div_le_div_right hn) 1))⟩
  choose p hp hl using hp
  let D : Finset V := univ.biUnion fun v : R => (p v).support.toFinset
  have hsub (v : R) : {w | w ∈ (p v).support} ⊆ (↑D : Set V) := by
    intro w hw
    exact mem_biUnion.mpr ⟨v,mem_univ _,List.mem_toFinset.mpr hw⟩
  have hrD : r ∈ D := hsub ⟨r,hr⟩ (Walk.start_mem_support _)
  refine ⟨D,?_,?_,?_⟩
  · have hre : ∀ v : (↑D : Set V), (G.induce (↑D : Set V)).Reachable ⟨r,hrD⟩ v := by
      rintro ⟨v,hv⟩
      obtain ⟨w,_,hw⟩ := mem_biUnion.mp hv
      have hh := ((p w).connected_induce_support).preconnected
        ⟨r,Walk.start_mem_support _⟩ ⟨v,List.mem_toFinset.mp hw⟩
      exact hh.map (G.induceHomOfLE (hsub w)).toHom
    exact {preconnected := fun v w => (hre v).symm.trans (hre w), nonempty := ⟨⟨r,hrD⟩⟩}
  · intro v
    obtain ⟨w,hw,hvw⟩ := hcover v (mem_univ _)
    exact ⟨w,hsub ⟨w,hw⟩ (Walk.end_mem_support _),hvw⟩
  · calc
      D.card ≤ ∑ v : R, (p v).support.toFinset.card := card_biUnion_le
      _ ≤ ∑ _v : R, 3*(N/k+1) := by
        apply sum_le_sum
        intro v _
        have he := (p v).length_support
        have hh := List.toFinset_card_le (p v).support
        have h := hl v
        omega
      _ = R.card * (3*(N/k+1)) := by simp [Nat.mul_comm]
      _ ≤ _ := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (3*(N/k+1)) hR

lemma neighbors_univ (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Density.neighbors G univ v = G.neighborFinset v := by ext; simp

lemma degree_delete (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (v : (↑(univ \ D) : Set V)) :
    G.degree v.val ≤ (G.induce (↑(univ \ D) : Set V)).degree v + D.card := by
  classical
  have he : ((G.induce (↑(univ \ D) : Set V)).neighborFinset v).image Subtype.val =
      G.neighborFinset v.val ∩ (univ \ D) := by
    ext w
    simp only [mem_image,mem_neighborFinset,induce_adj,mem_inter,mem_sdiff,mem_univ,true_and]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨hz,(mem_sdiff.mp z.property).2⟩
    · rintro ⟨hz,hD⟩
      exact ⟨⟨w,mem_sdiff.mpr ⟨mem_univ _,hD⟩⟩,hz,rfl⟩
  have hec := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective,card_neighborFinset_eq_degree] at hec
  have hu : G.neighborFinset v.val ⊆ G.neighborFinset v.val ∩ (univ \ D) ∪ D := by
    intro w hw
    by_cases hD : w ∈ D
    · exact mem_union_right _ hD
    · exact mem_union_left _ (mem_inter.mpr ⟨hw,mem_sdiff.mpr ⟨mem_univ _,hD⟩⟩)
  have hh := (card_le_card hu).trans (card_union_le _ _)
  rw [card_neighborFinset_eq_degree, ← hec] at hh
  exact hh

lemma clique_successor (G : SimpleGraph V) (D : Finset V)
    (hc : (G.induce (↑D : Set V)).Connected)
    (hd : ∀ v, ∃ w ∈ D, G.Adj v w) {q : ℕ}
    (hm : HasCliqueMinor (G.induce (↑(univ \ D) : Set V)) q) : HasCliqueMinor G (q+1) := by
  classical
  obtain ⟨B,hB,hdis,hE⟩ := hm
  let M := model_induce G (univ \ D)
  let C (i : Fin q) := M.expand (B i)
  have hC (i : Fin q) : (G.induce (C i)).Connected := M.expand_connected (hB i)
  have hCD (i : Fin q) : Disjoint (↑D : Set V) (C i) := by
    apply Set.disjoint_left.mpr
    rintro v hv ⟨w,_,hw⟩
    have he : v=w.val := hw
    exact (mem_sdiff.mp w.property).2 (he ▸ hv)
  have hCC (i j : Fin q) (hne : i≠j) : Disjoint (C i) (C j) := M.expand_disjoint (hdis i j hne)
  have had (i : Fin q) : ∃ v ∈ (↑D : Set V), ∃ w ∈ C i, G.Adj v w := by
    obtain ⟨w⟩ := (hC i).nonempty
    obtain ⟨v,hv,hvw⟩ := hd w.val
    exact ⟨v,hv,w.val,w.property,hvw.symm⟩
  have hCE (i j : Fin q) (hne : i≠j) : ∃ v ∈ C i, ∃ w ∈ C j, G.Adj v w := by
    obtain ⟨v,hv,w,hw,hvw⟩ := hE i j hne
    exact ⟨v.val,⟨v,hv,rfl⟩,w.val,⟨w,hw,rfl⟩,hvw⟩
  refine ⟨Fin.cases (↑D : Set V) C,?_,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hc
    · exact hC j
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b _ => ?_) j
      · exact fun h => (h rfl).elim
      · exact hCD b
    · refine Fin.cases (fun _ => ?_) (fun b h => ?_) j
      · exact (hCD a).symm
      · exact hCC a b (fun he => h (congrArg Fin.succ he))
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b _ => ?_) j
      · exact fun h => (h rfl).elim
      · exact had b
    · refine Fin.cases (fun _ => ?_) (fun b h => ?_) j
      · obtain ⟨v,hv,w,hw,hvw⟩ := had a
        exact ⟨w,hw,v,hv,hvw.symm⟩
      · exact hCE a b (fun he => h (congrArg Fin.succ he))

lemma component_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (w : (↑(G.connectedComponentMk v).supp.toFinset : Set V)) :
    (G.induce (↑(G.connectedComponentMk v).supp.toFinset : Set V)).degree w = G.degree w.val := by
  classical
  have he : ((G.induce (↑(G.connectedComponentMk v).supp.toFinset : Set V)).neighborFinset w).image
      Subtype.val = G.neighborFinset w.val := by
    ext z
    simp only [mem_image,mem_neighborFinset,induce_adj]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hz
      have hw : w.val ∈ (G.connectedComponentMk v).supp := by simpa using w.property
      have hy : z ∈ (G.connectedComponentMk v).supp.toFinset := by
        simpa using (G.connectedComponentMk v).mem_supp_of_adj_mem_supp hw hz
      exact ⟨⟨z,hy⟩,hz,rfl⟩
  have hh := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  simpa only [card_neighborFinset_eq_degree] using hh

theorem clique_of_min_degree (N k q : ℕ) (hk : 0<k)
    (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V ≤ N)
    (hd : ∀ v, k+q*domBudget N k ≤ G.degree v) : HasCliqueMinor G (q+1) := by
  classical
  induction q generalizing V with
  | zero => exact cliqueMinor_one G
  | succ q ih =>
    let v : V := Classical.arbitrary V
    let C : Finset V := (G.connectedComponentMk v).supp.toFinset
    let H := G.induce (↑C : Set V)
    have hC : H.Connected := by
      change (G.induce (↑(G.connectedComponentMk v).supp.toFinset : Set V)).Connected
      erw [Set.coe_toFinset]
      exact (G.connectedComponentMk v).connected_toSimpleGraph
    have : Nonempty (↑C : Set V) := hC.nonempty
    have hcard : Fintype.card (↑C : Set V) ≤ N := (Fintype.card_subtype_le _).trans hn
    have hdeg : ∀ w : (↑C : Set V), k+(q+1)*domBudget N k ≤ H.degree w := by
      intro w
      have he : H.degree w = G.degree w.val := component_degree G v w
      rw [he]
      exact hd w.val
    obtain ⟨D,hD,hdom,hsize⟩ := connected_dominating H hC hk hcard (fun w => by
      rw [neighbors_univ,card_neighborFinset_eq_degree]
      exact (Nat.le_add_right _ _).trans (hdeg w))
    change D.card ≤ domBudget N k at hsize
    have horder : D.card < Fintype.card (↑C : Set V) := by
      obtain ⟨w⟩ := hC.nonempty
      have hx := H.degree_lt_card_verts w
      have hh := hdeg w
      have hq : domBudget N k ≤ (q+1)*domBudget N k := by nlinarith
      omega
    have hR : (univ \ D).Nonempty := by
      apply card_pos.mp
      rw [card_sdiff_of_subset (subset_univ D),card_univ]
      omega
    have : Nonempty (↑(univ \ D) : Set (↑C : Set V)) := by
      obtain ⟨w,hw⟩ := hR; exact ⟨⟨w,hw⟩⟩
    have hdel : ∀ w : (↑(univ \ D) : Set (↑C : Set V)),
        k+q*domBudget N k ≤ (H.induce (↑(univ \ D) : Set (↑C : Set V))).degree w := by
      intro w
      have hx := degree_delete H D w
      have hh := hdeg w.val
      rw [Nat.add_mul,one_mul] at hh
      omega
    have hm := ih (↑(univ \ D) : Set (↑C : Set V))
      (H.induce (↑(univ \ D) : Set (↑C : Set V)))
      ((Fintype.card_subtype_le _).trans hcard) hdel
    exact (model_induce G C).lift_clique (clique_successor H D hD hdom hm)

lemma log64_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ Real.log (64*x) := by
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have h64 : (1:ℝ) ≤ Real.log 64 := by
    have he : (64:ℝ)=2^6 := by norm_num
    rw [he,Real.log_pow]
    norm_num at h2 ⊢
    linarith
  exact h64.trans (Real.log_le_log (by norm_num) (by linarith))

lemma domBudget_bound {k : ℕ} (hk : 2≤k) :
    (domBudget (32*k) (k/2) : ℝ) ≤ 100000*Real.log (64*k) := by
  have hk' : 0<k/2 := by omega
  have hratio : 32*k/(k/2) ≤96 := by
    have hh := Nat.mod_lt k (by omega : 0<2)
    have he := Nat.mod_add_div k 2
    have hm : k ≤3*(k/2) := by omega
    exact (Nat.div_le_iff_le_mul hk').mpr (by omega)
  have hr : ((32*k:ℕ):ℝ)/(3*(k/2:ℕ)) ≤32 := by
    have hm : k ≤3*(k/2) := by omega
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num
    exact_mod_cast hm
  have hlog : 1 ≤ Real.log (64*k) := log64_ge_one (by exact_mod_cast (show 1≤k by omega))
  have hval : 0 ≤ 10*(((32*k:ℕ):ℝ)/(3*(k/2:ℕ)))*Real.log (2*(32*k:ℕ)) := by
    have he : (2*(32*k:ℕ):ℝ) = 64*k := by push_cast; ring
    rw [he]; positivity
  have hceil := Nat.ceil_lt_add_one hval
  have he : (2*(32*k:ℕ):ℝ)=64*k := by push_cast; ring
  rw [he] at hceil
  have hv : 10*(((32*k:ℕ):ℝ)/(3*(k/2:ℕ)))*Real.log (64*k) ≤320*Real.log (64*k) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hb : (⌈10*(((32*k:ℕ):ℝ)/(3*(k/2:ℕ)))*Real.log (2*(32*k:ℕ))⌉₊:ℝ) ≤321*Real.log (64*k) := by
    rw [he]
    linarith
  unfold domBudget
  push_cast
  have hrat : (32*k/(k/2):ℕ) + (1:ℝ) ≤97 := by exact_mod_cast (show 32*k/(k/2)+1≤97 by omega)
  calc
    _ ≤ 291*(321*Real.log (64*k)) := by
      apply mul_le_mul
      · linarith
      · simpa only [Nat.cast_mul,Nat.cast_ofNat] using hb
      · positivity
      · norm_num
    _ ≤ _ := by nlinarith

theorem core_size_obstruction (G : SimpleGraph V) {t : ℕ} (ht : 2≤t)
    (hex : hadwigerNumber G < t) (hd : (16:ℚ)≤density G) :
    ∃ k : ℕ, 2≤k ∧ density G <8*(k+1) ∧
      (k:ℝ)<200000*t*Real.log (64*k) := by
  classical
  obtain ⟨n,k,H,⟨M⟩,hc,hn,hden⟩ := small_minor_core G hd
  have hk : 2≤k := by
    by_contra hh
    have hh : k≤1 := by omega
    have hh' : (k:ℚ)≤1 := by exact_mod_cast hh
    linarith
  have hn' : 0<n := by have hh:=hc.1; simpa using (Nat.zero_le k).trans_lt hh
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn'
  have hdeg : ∀ v, k≤H.degree v := by
    intro v
    simpa only [neighbors_univ,card_neighborFinset_eq_degree] using min_degree H hc (mem_univ v)
  have hnot : ¬ k/2+(t-1)*domBudget (32*k) (k/2) ≤ k := by
    intro hh
    have hm := clique_of_min_degree (32*k) (k/2) (t-1) (by omega) (Fin n) H
      (by simpa using hn) (fun v => hh.trans (hdeg v))
    have hle := cliqueMinor_le_hadwigerNumber (M.lift_clique hm)
    omega
  have hnat : k <2*t*domBudget (32*k) (k/2) := by
    have hh := Nat.mod_lt k (by omega : 0<2)
    have he := Nat.mod_add_div k 2
    have htM : (t-1)*domBudget (32*k) (k/2) ≤ t*domBudget (32*k) (k/2) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.mul_assoc]
    omega
  refine ⟨k,hk,hden,?_⟩
  have hr : (k:ℝ)<2*t*(domBudget (32*k) (k/2):ℝ) := by exact_mod_cast hnat
  have hb := domBudget_bound hk
  nlinarith

lemma logarithmic_inversion {x t : ℝ} (hx : 1≤x) (ht : 2≤t)
    (h : x<200000*t*Real.log (64*x)) : x<10400000*t*Real.log (2*t) := by
  have hx0 : 0<x := by linarith
  have ht0 : 0<t := by linarith
  have hs0 : 0<Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs1 : 1≤Real.sqrt x := by
    have hh := Real.sqrt_le_sqrt hx
    simpa using hh
  have hsq : (Real.sqrt x)^2=x := Real.sq_sqrt (by linarith)
  have hlog : Real.log (64*x) ≤8*Real.sqrt x := by
    have h1 := Real.log_le_sub_one_of_pos hs0
    rw [Real.log_sqrt (by linarith : 0≤x)] at h1
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have he : (64:ℝ)=2^6 := by norm_num
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0),he,Real.log_pow]
    norm_num at h2 ⊢
    linarith
  have hsl : Real.sqrt x<1600000*t := by
    have hh := mul_le_mul_of_nonneg_left hlog (show 0≤200000*t by positivity)
    nlinarith
  have hxx : x<(1600000*t)^2 := by nlinarith
  have hpow : 64*x≤(2:ℝ)^50*t^2 := by nlinarith [sq_nonneg t]
  have hll := Real.log_le_log (show 0<64*x by positivity) hpow
  rw [Real.log_mul (show (2:ℝ)^50≠0 by norm_num) (show t^2≠0 by positivity),Real.log_pow,Real.log_pow] at hll
  have h2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have htt : 0≤Real.log t := Real.log_nonneg (by linarith)
  have hl : Real.log (64*x) ≤52*Real.log (2*t) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt ht0)]
    norm_num at hll
    linarith
  have hh := mul_le_mul_of_nonneg_left hl (show 0≤200000*t by positivity)
  nlinarith

theorem density_bound (G : SimpleGraph V) {t : ℕ} (ht : 2≤t)
    (hex : hadwigerNumber G<t) :
    ((density G : ℚ):ℝ) ≤100000000*t*Real.log (2*t) := by
  classical
  have htr : (2:ℝ)≤t := by exact_mod_cast ht
  have hlog : 1≤Real.log (2*t) := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    have h4 : (1:ℝ)≤Real.log 4 := by
      have he : (4:ℝ)=2^2 := by norm_num
      rw [he,Real.log_pow]
      norm_num at h2 ⊢
      linarith
    exact h4.trans (Real.log_le_log (by norm_num) (by linarith))
  by_cases hd : (16:ℚ)≤density G
  · obtain ⟨k,hk,hden,hx⟩ := core_size_obstruction G ht hex hd
    have hr := logarithmic_inversion (by exact_mod_cast (show 1≤k by omega)) htr hx
    have hd' : ((density G:ℚ):ℝ)<8*((k:ℝ)+1) := by exact_mod_cast hden
    have hh : (2:ℝ)≤(t:ℝ)*Real.log (2*t) := by nlinarith
    nlinarith
  · have hd' : ((density G:ℚ):ℝ)<16 := by exact_mod_cast (lt_of_not_ge hd)
    nlinarith

lemma degree_induce_finset {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (v : (↑S : Set V)) : (G.induce (↑S : Set V)).degree v = (S.filter (G.Adj v.val)).card := by
  classical
  have he : ((G.induce (↑S : Set V)).neighborFinset v).image Subtype.val = S.filter (G.Adj v.val) := by
    ext w
    simp only [mem_image,mem_neighborFinset,induce_adj,mem_filter]
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,hu⟩
    · rintro ⟨hw,hvw⟩
      exact ⟨⟨w,hw⟩,hvw,rfl⟩
  have hh := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective,card_neighborFinset_eq_degree] at hh
  exact hh

end LinearListHadwiger.CoarseDensity

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Incidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Incidence
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V  :  Type} [Fintype V] [DecidableEq V]

lemma hit_pool {V : Type} [Fintype V] [DecidableEq V] {I  :  Type} [Fintype I] (A  :  Finset V) (hA  :  A.Nonempty)
    (R  :  I → V → Prop) [DecidableRel R] (s  :  ℕ) (p  :  ℝ) (hp  :  0 ≤ p)
    (hmiss  :  ∀ i ,  ((A.filter fun v  =>  ¬ R i v).card : ℝ)  ≤  p * A.card)
    (hsmall  :  (Fintype.card I : ℝ) * p ^ s < 1)  :
    ∃ B ⊆ A ,  B.card ≤ s  ∧  ∀ i ,  ∃ v ∈ B ,  R i v  :=  by
  classical
  have hpos : (0 : ℝ) < A.card := by exact_mod_cast card_pos.mpr hA

  let w'  :  A → ℝ  :=  fun _  => (A.card : ℝ)⁻¹
  have hsum'  :  ∑ v  :  A ,  w' v = 1  :=  by
    simp only [w' , sum_const , card_univ , Fintype.card_coe , nsmul_eq_mul]
    exact mul_inv_cancel₀ hpos.ne'
  have hrow (i  :  I)  :  ∑ v  :  A ,  w' v * (if  ¬ R i v.val then 1 else 0)  ≤ p  :=  by
    have he  :  (univ.filter fun v  :  A  =>  ¬ R i v.val).card  =  (A.filter fun v  =>  ¬ R i v).card  :=  by
      apply card_bij (fun v _  => v.val)
      · intro v hv; exact mem_filter.mpr ⟨v.property , (mem_filter.mp hv).2⟩
      · intro v _ u _ he; exact Subtype.ext he
      · intro v hv; exact ⟨⟨v , (mem_filter.mp hv).1⟩ , mem_filter.mpr ⟨mem_univ _ , (mem_filter.mp hv).2⟩ , rfl⟩
    calc
      _  =  ((A.filter fun v  =>  ¬ R i v).card : ℝ) / A.card  :=  by
        simp only [w' , mul_ite , mul_one , mul_zero]
        rw [←sum_filter , sum_const , he]
        simp only [nsmul_eq_mul , div_eq_mul_inv]
      _  ≤  p  :=  (div_le_iff₀ hpos).mpr (hmiss i)
  obtain ⟨f , hf⟩  :=  ConnectivityTests.finite_hitting s w' (fun _  => by dsimp [w']; positivity)
    hsum' (fun i (v : A)  => R i v.val) p hp hrow hsmall
  refine ⟨univ.image (fun i  => (f i).val) , ?_ , ?_ , ?_⟩
  · intro v hv; obtain ⟨i , _ , rfl⟩  :=  mem_image.mp hv; exact (f i).property
  · exact (card_image_le).trans (by simp)
  · intro i
    obtain ⟨j , hj⟩  :=  hf i
    exact ⟨_ , mem_image.mpr ⟨j , mem_univ _ , rfl⟩ , hj⟩

lemma star_connected {V : Type} [Fintype V] [DecidableEq V] (G  :  SimpleGraph V) (c  :  V) (B  :  Finset V)
    (hB  :  ∀ v ∈ B ,  G.Adj c v)  :  (G.induce (↑(insert c B) : Set V)).Connected  :=  by
  classical
  have hc  :  c ∈ insert c B  :=  mem_insert_self _ _
  have hr  :  ∀ v  :  (↑(insert c B) : Set V) ,
      (G.induce (↑(insert c B) : Set V)).Reachable ⟨c , hc⟩ v  :=  by
    intro v
    by_cases he  :  v.val = c
    · have he'  :  v = ⟨c , hc⟩  :=  Subtype.ext he
      subst v; exact Reachable.rfl
    · have hv  :  v.val ∈ B  :=  mem_of_mem_insert_of_ne v.property he
      exact (show (G.induce (↑(insert c B) : Set V)).Adj ⟨c , hc⟩ v from hB v.val hv).reachable
  exact {preconnected  :=  fun v w  => (hr v).symm.trans (hr w) , nonempty  :=  ⟨⟨c , hc⟩⟩}

lemma fresh_star (G  :  SimpleGraph V) [DecidableRel G.Adj]
    (Z  :  Finset V) {q s  :  ℕ} (reps  :  Fin q → V) {d  :  ℝ}
    (hn  :  0 < Fintype.card V)
    (hz  :  2 * Z.card ≤ Fintype.card V)
    (hd  :  0 ≤ d) (hdsmall  :  4 * d ≤ Fintype.card V)
    (hdeg  :  ∀ v ,  ((univ.filter fun w  =>  ¬ G.Adj v w).card : ℝ) ≤ d)
    (hsmall  :  (q : ℝ) * (4 * d/Fintype.card V) ^ s < 1)  :
    ∃ D  :  Finset V ,  Disjoint D Z  ∧  (G.induce (↑D : Set V)).Connected  ∧
      D.card ≤ s + 1  ∧  ∀ i ,  ∃ v ∈ D ,  G.Adj (reps i) v  :=  by
  classical
  have hR  :  (univ\Z).Nonempty  :=  by
    apply card_pos.mp
    rw [card_sdiff_of_subset (subset_univ Z) , card_univ]
    omega
  obtain ⟨c , hc⟩  :=  hR
  let A  :  Finset V  :=  (univ\Z).filter (G.Adj c)
  have hcard  :  (Fintype.card V : ℝ)/4  ≤  A.card  :=  by
    have hbad  :=  hdeg c
    have hcover  :  univ  ⊆  Z ∪ A ∪ univ.filter (fun w  =>  ¬ G.Adj c w)  :=  by
      intro v _
      by_cases hv  :  v ∈ Z
      · exact mem_union_left _ (mem_union_left _ hv)
      · by_cases he  :  G.Adj c v
        · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _ , hv⟩ , he⟩))
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _ , he⟩)
    have hnat  :=  (card_le_card hcover).trans (card_union_le _ _)
    have hun  :=  card_union_le Z A
    have hz'  :  2 * (Z.card : ℝ) ≤ Fintype.card V  :=  by exact_mod_cast hz
    have hnat'  :  (Fintype.card V : ℝ) ≤ (Z∪A).card + (univ.filter fun w  =>  ¬ G.Adj c w).card  :=  by
      exact_mod_cast hnat
    have hun'  :  ((Z∪A).card : ℝ) ≤ Z.card + A.card  :=  by exact_mod_cast hun
    linarith
  have hA  :  A.Nonempty  :=  by
    apply card_pos.mp
    have hn'  :  (0 : ℝ) < Fintype.card V  :=  by exact_mod_cast hn
    have hh  :  (0 : ℝ) < A.card  :=  by linarith
    exact_mod_cast hh
  have hmiss (i  :  Fin q)  :  ((A.filter fun v  =>  ¬ G.Adj (reps i) v).card : ℝ)  ≤
      (4 * d/Fintype.card V) * A.card  :=  by
    have hsub  :  A.filter (fun v  =>  ¬ G.Adj (reps i) v)  ⊆  univ.filter (fun v  =>  ¬ G.Adj (reps i) v)  :=
      filter_subset_filter _ (subset_univ _)
    have hh  :  ((A.filter fun v  =>  ¬ G.Adj (reps i) v).card : ℝ) ≤ d  :=
      by
      have hg : ((A.filter fun v => ¬ G.Adj (reps i) v).card : ℝ) ≤
          (univ.filter fun v => ¬ G.Adj (reps i) v).card := by exact_mod_cast card_le_card hsub
      exact hg.trans (hdeg (reps i))
    have hn'  :  (0 : ℝ) < Fintype.card V  :=  by exact_mod_cast hn
    have hx  :  d  ≤  (4 * d/Fintype.card V) * A.card  :=  by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hn').mpr
      nlinarith
    exact hh.trans hx
  obtain ⟨B , hBA , hBs , hhit⟩  :=  hit_pool A hA (fun i v  => G.Adj (reps i) v) s
    (4 * d/Fintype.card V) (by positivity) hmiss (by simpa using hsmall)
  refine ⟨insert c B , ?_ , star_connected G c B (fun v hv  => (mem_filter.mp (hBA hv)).2) , ?_ , ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hzv
    rcases mem_insert.mp hv with he|hv
    · subst v; exact (mem_sdiff.mp hc).2 hzv
    · exact (mem_sdiff.mp (mem_filter.mp (hBA hv)).1).2 hzv
  · exact (card_insert_le _ _).trans (by omega)
  · intro i; obtain ⟨v , hv , he⟩  :=  hhit i
    exact ⟨v , mem_insert_of_mem hv , he⟩

lemma BoundedBags.minor {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {q b : ℕ} (B : BoundedBags G q b) :
    HasCliqueMinor G q :=
  ⟨fun i => ↑(B.bag i), B.connected,
    fun i j h => Finset.disjoint_coe.mpr (B.disjoint i j h),B.adjacent⟩

lemma BoundedBags.succ {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {q b : ℕ} (B : BoundedBags G q b)
    (D : Finset V) (hc : (G.induce (↑D:Set V)).Connected)
    (hd : ∀ i, Disjoint D (B.bag i)) (hs : D.card ≤ b)
    (ha : ∀ i, ∃ v ∈ D, ∃ w ∈ B.bag i, G.Adj v w) :
    Nonempty (BoundedBags G (q+1) b) := by
  classical
  refine ⟨{bag := Fin.cases D B.bag,connected := ?_, disjoint := ?_,adjacent := ?_,small := ?_}⟩
  · intro i; exact Fin.cases hc B.connected i
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases (fun h => (h rfl).elim) (fun b _ => hd b) j
    · refine Fin.cases (fun _ => (hd a).symm) (fun b h => ?_) j
      exact B.disjoint a b (fun he => h (congrArg Fin.succ he))
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases (fun h => (h rfl).elim) (fun b _ => ha b) j
    · refine Fin.cases (fun _ => ?_) (fun b h => ?_) j
      · obtain ⟨v,hv,w,hw,he⟩ := ha a
        exact ⟨w,hw,v,hv,he.symm⟩
      · exact B.adjacent a b (fun he => h (congrArg Fin.succ he))
  · intro i; exact Fin.cases hs B.small i

theorem near_complete_minor (G : SimpleGraph V) [DecidableRel G.Adj]
    {t s : ℕ} {d : ℝ} (hn : 0<Fintype.card V)
    (hnlarge : 2*t*(s+1)≤Fintype.card V)
    (hd : 0≤d) (hdsmall : 4*d≤Fintype.card V)
    (hdeg : ∀ v, ((univ.filter fun w => ¬G.Adj v w).card:ℝ)≤d)
    (hsmall : (t:ℝ)*(4*d/Fintype.card V)^s<1) : HasCliqueMinor G t := by
  classical
  have all (q : ℕ) (hq : q≤t) : Nonempty (BoundedBags G q (s+1)) := by
    induction q with
    | zero =>
      exact ⟨{ bag := Fin.elim0
               connected := fun i => Fin.elim0 i
               disjoint := fun i => Fin.elim0 i
               adjacent := fun i => Fin.elim0 i
               small := fun i => Fin.elim0 i }⟩
    | succ q ih =>
      obtain ⟨B⟩ := ih (by omega)
      let Z := univ.biUnion B.bag
      have hZ : Z.card ≤ q*(s+1) := by
        calc
          _ ≤ ∑ i, (B.bag i).card := card_biUnion_le
          _ ≤ ∑ _i : Fin q, (s+1) := sum_le_sum (fun i _ => B.small i)
          _ = _ := by simp
      have hz : 2*Z.card ≤ Fintype.card V := by nlinarith
      have hr : ∀ i, ∃ v, v ∈ B.bag i := by
        intro i
        obtain ⟨v⟩ := (B.connected i).nonempty
        exact ⟨v.val,v.property⟩
      choose reps hreps using hr
      have hqsmall : (q:ℝ)*(4*d/Fintype.card V)^s<1 := by
        have hq' : (q:ℝ)≤t := by exact_mod_cast (show q≤t by omega)
        exact (mul_le_mul_of_nonneg_right hq' (by positivity)).trans_lt hsmall
      obtain ⟨D,hDZ,hDc,hDs,hDa⟩ := fresh_star G Z reps hn hz hd hdsmall hdeg hqsmall
      apply B.succ D hDc (fun i => Disjoint.mono_right (subset_biUnion_of_mem B.bag (mem_univ i)) hDZ) hDs
      intro i
      obtain ⟨v,hv,he⟩ := hDa i
      exact ⟨v,hv,reps i,hreps i,he.symm⟩
  obtain ⟨B⟩ := all t le_rfl
  exact B.minor

theorem missing_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    {t s : ℕ} {δ : ℝ} (ht : 1 ≤ t)
    (hex : ¬ HasCliqueMinor G t)
    (hn : 2*t*(s+1) ≤ Fintype.card V)
    (hδ : 0 ≤ δ) (hδsmall : 8*δ ≤ 1)
    (hδn : 1 ≤ δ*Fintype.card V)
    (hprob : (t:ℝ)*(8*δ)^s < 1) :
    ∃ v, δ*Fintype.card V ≤ ((univ.filter fun w => w ≠ v ∧ ¬G.Adj v w).card : ℝ) := by
  classical
  by_contra hc
  push Not at hc
  have hcard : 0<Fintype.card V := by nlinarith
  have hdeg (v : V) : ((univ.filter fun w => ¬G.Adj v w).card : ℝ) ≤ 2*δ*Fintype.card V := by
    have he : univ.filter (fun w => ¬G.Adj v w) =
        insert v (univ.filter fun w => w ≠ v ∧ ¬G.Adj v w) := by
      ext w
      simp only [mem_filter,mem_univ,true_and,mem_insert]
      by_cases hw : w=v
      · subst w; simp
      · simp [hw]
    rw [he,card_insert_of_notMem (by simp)]
    push_cast
    linarith [hc v]
  apply hex
  apply near_complete_minor G hcard hn (d := 2*δ*Fintype.card V) (by positivity)
  · have hn' : (0:ℝ) ≤ Fintype.card V := by positivity
    nlinarith
  · exact hdeg
  · have hn' : (Fintype.card V:ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
    convert hprob using 1; field_simp; ring

lemma addStar_le {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (u : V) (N : Finset V) : H ≤ addStar H u N :=
  fun _ _ h => Or.inl h

lemma addStar_edges (H : SimpleGraph V) (u : V) (N : Finset V) :
    H.edgeFinset.card + (N.filter fun w => w ≠ u ∧ ¬ H.Adj u w).card ≤
      (addStar H u N).edgeFinset.card := by
  classical
  let M := N.filter fun w => w ≠ u ∧ ¬ H.Adj u w
  let E := M.image fun w => s(u,w)
  have hinj : Set.InjOn (fun w : V => s(u,w)) (↑M : Set V) := by
    intro a ha b hb he
    rcases Sym2.eq_iff.mp he with he | he
    · exact he.2
    · exact he.2.trans he.1
  have hcard : E.card = M.card := card_image_of_injOn hinj
  have hdis : Disjoint H.edgeFinset E := by
    apply Finset.disjoint_left.mpr
    intro e he hg
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hg
    exact (mem_filter.mp hw).2.2 (by simpa using he)
  have hsub : H.edgeFinset ∪ E ⊆ (addStar H u N).edgeFinset := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact SimpleGraph.edgeFinset_mono (addStar_le H u N) he
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp he
      have hw' := mem_filter.mp hw
      exact SimpleGraph.mem_edgeFinset.mpr (Or.inr (Or.inl ⟨rfl,hw'.1,hw'.2.1.symm⟩))
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis,hcard] at hc
  exact hc

lemma missing_in_set {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (N : Finset V)
    {t s : ℕ} {δ : ℝ} (ht : 1 ≤ t) (hex : ¬ HasCliqueMinor H t)
    (hn : 2*t*(s+1) ≤ N.card) (hδ : 0 ≤ δ) (hδsmall : 8*δ ≤ 1)
    (hδn : 1 ≤ δ*N.card) (hprob : (t:ℝ)*(8*δ)^s < 1) :
    ∃ u ∈ N, δ*N.card ≤ ((N.filter fun w => w ≠ u ∧ ¬H.Adj u w).card : ℝ) := by
  classical
  let J := H.induce (↑N : Set V)
  have hn' : 2*t*(s+1) ≤ Fintype.card (↑N : Set V) := by simpa using hn
  have hex' : ¬HasCliqueMinor J t := fun hh => hex ((Knitting.model_induce H N).lift_clique hh)
  have hδn' : 1 ≤ δ*Fintype.card (↑N : Set V) := by simpa using hδn
  obtain ⟨u,hu⟩ := missing_vertex J ht hex' hn' hδ hδsmall hδn' hprob
  have he : (univ.filter fun w : (↑N : Set V) => w ≠ u ∧ ¬J.Adj u w).card =
      (N.filter fun w => w ≠ u.val ∧ ¬H.Adj u.val w).card := by
    apply card_bij (fun w _ => w.val)
    · intro w hw
      obtain ⟨hw₁,hw₂⟩ := (mem_filter.mp hw).2
      exact mem_filter.mpr ⟨w.property,(fun he => hw₁ (Subtype.ext he)),hw₂⟩
    · intro a _ b _ he; exact Subtype.ext he
    · intro w hw
      obtain ⟨hwN,hwU,hwE⟩ := mem_filter.mp hw
      refine ⟨⟨w,hwN⟩,mem_filter.mpr ⟨mem_univ _,?_,hwE⟩,rfl⟩
      exact fun hh => hwU (congrArg Subtype.val hh)
  refine ⟨u.val,u.property,?_⟩
  have hcn : Fintype.card (↑N : Set V) = N.card := by simp
  rw [hcn,he] at hu
  exact hu

lemma filter_subtype_card {V : Type} [Fintype V] [DecidableEq V] (A : Finset V) (p : V → Prop) :
    (univ.filter fun a : (↑A : Set V) => p a.val).card = (A.filter p).card := by
  classical
  apply card_bij (fun a _ => a.val)
  · intro a ha; exact mem_filter.mpr ⟨a.property,(mem_filter.mp ha).2⟩
  · intro a _ b _ he; exact Subtype.ext he
  · intro v hv
    exact ⟨⟨v,(mem_filter.mp hv).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩,rfl⟩

theorem incidence_model (P : SimpleGraph V) (A T : Finset V)
    {t s : ℕ} {δ : ℝ} (ht : 1 ≤ t) (hex : ¬ HasCliqueMinor P t)
    (hdis : Disjoint A T)
    (hlarge : ∀ v ∈ T, 2*t*(s+1) ≤ (A.filter (P.Adj v)).card)
    (hδ : 0 ≤ δ) (hδsmall : 8*δ ≤ 1)
    (hδn : 1 ≤ δ*(2*t*(s+1))) (hprob : (t:ℝ)*(8*δ)^s < 1) :
    ∃ (H : SimpleGraph (↑A : Set V)) (M : MinorModel P H),
      (∀ a, a.val ∈ M.branch a) ∧
      (∀ a, M.branch a ⊆ (↑(A∪T) : Set V)) ∧
      δ*(∑ v ∈ T, ((A.filter (P.Adj v)).card : ℝ)) ≤ H.edgeFinset.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    let H : SimpleGraph (↑A : Set V) := ⊥
    let M : MinorModel P H :=
      { branch := fun a => {a.val}
        connected := fun a => by
          have : Nonempty ({a.val} : Set V) := ⟨⟨a.val,rfl⟩⟩
          exact Connected.of_subsingleton
        disjoint := fun a b hn => Set.disjoint_singleton.mpr (fun he => hn (Subtype.ext he))
        adjacent := by intro a b h; exact h.elim }
    refine ⟨H,M,fun a => rfl,?_,?_⟩
    · intro a v hv
      have he : v=a.val := hv
      simp [he,a.property]
    · simp
  | @insert v T hvT ih =>
    have hdisT : Disjoint A T := Finset.disjoint_of_subset_right (subset_insert _ _) hdis
    have hvA : v ∉ A := fun hh => Finset.disjoint_left.mp hdis hh (mem_insert_self _ _)
    obtain ⟨H,M,hroot,hsupp,hcount⟩ := ih hdisT (fun w hw => hlarge w (mem_insert_of_mem hw))
    let N : Finset (↑A:Set V) := univ.filter fun a => P.Adj v a.val
    have hNc : N.card = (A.filter (P.Adj v)).card := filter_subtype_card A (P.Adj v)
    have hNlarge : 2*t*(s+1) ≤ N.card := by rw [hNc]; exact hlarge v (mem_insert_self _ _)
    have hNm : 1 ≤ δ*N.card := by
      have hN' : (2:ℝ)*t*(s+1) ≤ N.card := by exact_mod_cast hNlarge
      exact hδn.trans (mul_le_mul_of_nonneg_left hN' hδ)
    have hexH : ¬ HasCliqueMinor H t := fun h => hex (M.lift_clique h)
    obtain ⟨u,hu,hgain⟩ := missing_in_set H N ht hexH hNlarge hδ hδsmall hNm hprob
    have hvM : ∀ a, v ∉ M.branch a := by
      intro a ha
      rcases mem_union.mp (hsupp a ha) with hh | hh
      · exact hvA hh
      · exact hvT hh
    let M' := extendModel M Subtype.val hroot v hvM N (fun a ha => (mem_filter.mp ha).2) u hu
    have hnew := addStar_edges H u N
    refine ⟨addStar H u N,M',?_,?_,?_⟩
    · intro a
      change a.val ∈ if a=u then insert v (M.branch a) else M.branch a
      split_ifs <;> simp [hroot]
    · intro a w hw
      change w ∈ (if a=u then insert v (M.branch a) else M.branch a) at hw
      split_ifs at hw with ha
      · rcases hw with rfl | hw
        · exact mem_union_right _ (mem_insert_self _ _)
        · rcases mem_union.mp (hsupp a hw) with hw | hw
          · exact mem_union_left _ hw
          · exact mem_union_right _ (mem_insert_of_mem hw)
      · rcases mem_union.mp (hsupp a hw) with hw | hw
        · exact mem_union_left _ hw
        · exact mem_union_right _ (mem_insert_of_mem hw)
    · have hnew' : (H.edgeFinset.card:ℝ) + (N.filter fun w => w ≠ u ∧ ¬H.Adj u w).card ≤
          (addStar H u N).edgeFinset.card := by exact_mod_cast hnew
      rw [sum_insert hvT]
      rw [hNc] at hgain
      nlinarith

theorem incidence_finite (P : SimpleGraph V) (A T : Finset V)
    {t s : ℕ} {δ : ℝ} (ht : 2 ≤ t) (hex : hadwigerNumber P < t)
    (hdis : Disjoint A T)
    (hlarge : ∀ v ∈ T, 2*t*(s+1) ≤ (A.filter (P.Adj v)).card)
    (hδ : 0 ≤ δ) (hδsmall : 8*δ ≤ 1)
    (hδn : 1 ≤ δ*(2*t*(s+1))) (hprob : (t:ℝ)*(8*δ)^s < 1) :
    δ*(∑ v ∈ T, ((A.filter (P.Adj v)).card : ℝ)) ≤
      100000000*t*Real.log (2*t)*A.card := by
  classical
  by_cases hA : A = ∅
  · simp [hA]
  have hn : 0 < Fintype.card (↑A : Set V) := by simpa using card_pos.mpr (nonempty_iff_ne_empty.mpr hA)
  obtain ⟨H,M,_,_,hcount⟩ := incidence_model P A T (by omega) (fun h => (not_lt_of_ge (cliqueMinor_le_hadwigerNumber h)) hex)
    hdis hlarge hδ hδsmall hδn hprob
  have hd := CoarseDensity.density_bound H ht (M.hadwiger_le.trans_lt hex)
  have he : (H.edgeFinset.card : ℝ) = ((Knitting.density H : ℚ):ℝ)*A.card := by
    have hh := Knitting.density_mul_order H hn
    have hh' : ((Knitting.density H : ℚ):ℝ)*Fintype.card (↑A : Set V) = H.edgeFinset.card := by exact_mod_cast hh
    simpa using hh'.symm
  exact hcount.trans (he.le.trans (mul_le_mul_of_nonneg_right hd (by positivity)))

open Filter in
lemma incidence_cutoff : ∀ᶠ z : ℝ in atTop,
    2 ≤ z ∧ 8*z^(-(1/200:ℝ)) ≤ 1 ∧
    1 ≤ z^(-(1/200:ℝ))*(2*z*(1600+1)) ∧
    z*(8*z^(-(1/200:ℝ)))^1600 < 1 ∧
    100000000*Real.log (2*z) ≤ z^(1/200:ℝ) := by
  have hsmall : ∀ᶠ z : ℝ in atTop, 8*z^(-(1/200:ℝ)) ≤ 1 := by
    have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/200)).const_mul 8
    apply Tendsto.eventually_le_const (by norm_num : (8:ℝ)*0<1) hh
  have hprob : ∀ᶠ z : ℝ in atTop, (8:ℝ)^1600 * z^(-(7:ℝ)) < 1 := by
    have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7)).const_mul ((8:ℝ)^1600)
    apply Tendsto.eventually_lt_const (by simp : (8:ℝ)^1600*0<1) hh
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/200)).bound
    (show (0:ℝ)<1/200000000 by norm_num)
  have hconst : ∀ᶠ z : ℝ in atTop, 200000000*Real.log 2 ≤ z^(1/200:ℝ) :=
    (tendsto_atTop.mp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/200))) _
  filter_upwards [eventually_ge_atTop (2:ℝ),hsmall,hprob,hlog,hconst] with z hz hs hp hl hc
  have hzpos : 0<z := by linarith
  have hzone : 1≤z := by linarith
  refine ⟨hz,hs,?_,?_,?_⟩
  · have hpow : z^(-(1/200:ℝ))*z = z^(199/200:ℝ) := by
      rw [←Real.rpow_add_one hzpos.ne']
      norm_num
    have hone := Real.one_le_rpow hzone (show (0:ℝ)≤199/200 by norm_num)
    calc
      _ = 3202*(z^(-(1/200:ℝ))*z) := by ring
      _ = 3202*z^(199/200:ℝ) := by rw [hpow]
      _ ≥ 1 := by linarith
  · have hpw : (z^(-(1/200:ℝ)))^1600 = z^(-(8:ℝ)) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hzpos.le]
      norm_num
    have he : z*z^(-(8:ℝ))=z^(-(7:ℝ)) := by
      calc
        _ = z^(1:ℝ)*z^(-(8:ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hzpos]; norm_num
    calc
      _ = (8:ℝ)^1600 * (z*(z^(-(1/200:ℝ)))^1600) := by rw [mul_pow]; ac_rfl
      _ = (8:ℝ)^1600 * z^(-(7:ℝ)) := by rw [hpw,he]
      _ < 1 := hp
  · have hl' : Real.log z ≤ (1:ℝ)/200000000*z^(1/200:ℝ) := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hzone),
        abs_of_nonneg (Real.rpow_nonneg hzpos.le _)] using hl
    rw [Real.log_mul (by norm_num) hzpos.ne']
    linarith

theorem incidence_bound : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (P : SimpleGraph W),
    hadwigerNumber P < t → ∀ A T : Finset W, Disjoint A T →
    (∑ v ∈ T.filter (fun v => 3202*t ≤ (A.filter (P.Adj v)).card),
      ((A.filter (P.Adj v)).card : ℝ)) ≤ (t:ℝ)^(101/100:ℝ)*A.card := by
  classical
  obtain ⟨t₀,ht₀⟩ := Filter.eventually_atTop.mp incidence_cutoff.natCast_atTop
  refine ⟨t₀,?_⟩
  intro t htt W _ _ P hex A T hdis
  obtain ⟨ht,hs,hn,hp,hl⟩ := ht₀ t htt
  have htn : 2≤t := by exact_mod_cast ht
  have htpos : (0:ℝ)<t := by linarith
  let T' := T.filter (fun v => 3202*t ≤ (A.filter (P.Adj v)).card)
  have hdis' : Disjoint A T' := Finset.disjoint_of_subset_right (filter_subset _ _) hdis
  have hlarge : ∀ v ∈ T', 2*t*(1600+1) ≤ (A.filter (P.Adj v)).card := by
    intro v hv
    have hh := (mem_filter.mp hv).2
    nlinarith
  have hδ : (0:ℝ)<(t:ℝ)^(-(1/200:ℝ)) := Real.rpow_pos_of_pos htpos _
  have hh := incidence_finite P A T' htn hex hdis' hlarge hδ.le hs hn hp
  have he : (t:ℝ)^(-(1/200:ℝ))*(t:ℝ)^(101/100:ℝ) = (t:ℝ)*(t:ℝ)^(1/200:ℝ) := by
    calc
      _ = (t:ℝ)^((-(1/200:ℝ))+(101/100:ℝ)) := (Real.rpow_add htpos _ _).symm
      _ = (t:ℝ)^((1:ℝ)+(1/200:ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add htpos,Real.rpow_one]
  apply (mul_le_mul_iff_right₀ hδ).mp
  calc
    _ ≤ 100000000*t*Real.log (2*t)*A.card := hh
    _ = (t:ℝ)*(100000000*Real.log (2*t))*A.card := by ring
    _ ≤ (t:ℝ)*(t:ℝ)^(1/200:ℝ)*A.card := by gcongr
    _ = (t:ℝ)^(-(1/200:ℝ))*((t:ℝ)^(101/100:ℝ)*A.card) := by rw [←mul_assoc,he]

end LinearListHadwiger.Incidence

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.District
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.District
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

theorem restricted_degree_loss (G : SimpleGraph V) (H S : Finset V) (hHS : H ⊆ S) :
    (∑ v ∈ H, (S.filter (G.Adj v)).card) ≤
      (S ∩ outside G H).card + loss2 G H := by
  rw [degree_sum_split,inter_eq_right.mpr hHS,←darts_sum]
  have hs : ∑ w ∈ S ∩ outside G H, ((H.filter (G.Adj w)).card-1) ≤
      ∑ w ∈ outside G H, ((H.filter (G.Adj w)).card-1) := sum_le_sum_of_subset inter_subset_right
  have hc : ∑ w ∈ S ∩ outside G H, (H.filter (G.Adj w)).card =
      (S ∩ outside G H).card + ∑ w ∈ S ∩ outside G H, ((H.filter (G.Adj w)).card-1) := by
    rw [show (S ∩ outside G H).card = (∑ _w ∈ S ∩ outside G H, (1:ℕ)) by simp,←sum_add_distrib]
    apply sum_congr rfl
    intro w hw
    have hh := outside_pos G H (mem_inter.mp hw).2
    omega
  rw [hc]
  unfold loss2
  omega

lemma outside_insert (G : SimpleGraph V) (H : Finset V) {w : V}
    (hw : w ∈ outside G H) :
    outside G (insert w H) = (outside G H).erase w ∪ (G.neighborFinset w \ H) := by
  ext z
  simp only [mem_outside,mem_insert,not_or,mem_union,mem_erase,mem_sdiff,SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨⟨hzw,hzH⟩,v,(rfl|hv),h⟩
    · exact Or.inr ⟨h,hzH⟩
    · exact Or.inl ⟨hzw,⟨hzH,v,hv,h⟩⟩
  · rintro (⟨hzw,hzH,v,hv,h⟩|⟨h,hzH⟩)
    · exact ⟨⟨hzw,hzH⟩,v,Or.inr hv,h⟩
    · exact ⟨⟨h.ne.symm,hzH⟩,w,Or.inl rfl,h⟩

lemma neighborhood_increment (G : SimpleGraph V) (H : Finset V) {w : V}
    (hw : w ∈ outside G H) :
    (outside G (insert w H)).card + ((outside G H).filter (G.Adj w)).card +
      (H.filter (G.Adj w)).card + 1 = (outside G H).card + G.degree w := by
  have hi : (outside G H).erase w ∩ (G.neighborFinset w \ H) =
      (outside G H).filter (G.Adj w) := by
    ext z
    simp only [mem_inter,mem_erase,mem_sdiff,SimpleGraph.mem_neighborFinset,mem_filter]
    constructor
    · rintro ⟨⟨_,hz⟩,h,_⟩; exact ⟨hz,h⟩
    · rintro ⟨hz,h⟩; exact ⟨⟨h.ne.symm,hz⟩,h,((mem_outside _ _ _).mp hz).1⟩
  have hc := card_union_add_card_inter ((outside G H).erase w) (G.neighborFinset w \ H)
  rw [←outside_insert G H hw,hi,card_erase_of_mem hw] at hc
  have he : G.neighborFinset w ∩ H = H.filter (G.Adj w) := by ext z; simp [and_comm]
  have hd := card_sdiff_add_card_inter (G.neighborFinset w) H
  rw [he,SimpleGraph.card_neighborFinset_eq_degree] at hd
  have hp := card_pos.mpr ⟨w,hw⟩
  omega

lemma loss2_insert (G : SimpleGraph V) (H : Finset V) {w : V}
    (hw : w ∈ outside G H) :
    loss2 G (insert w H) = loss2 G H + 2*(1+((outside G H).filter (G.Adj w)).card) := by
  have hwH := ((mem_outside _ _ _).mp hw).1
  have h1 := loss2_identity G H
  have h2 := loss2_identity G (insert w H)
  have h3 := neighborhood_increment G H hw
  have h4 := Density.darts_erase G (mem_insert_self w H)
  rw [erase_insert hwH] at h4
  have hn : Density.neighbors G (insert w H) w = H.filter (G.Adj w) := by
    ext z
    simp only [Density.mem_neighbors,mem_insert,mem_filter]
    exact ⟨fun ⟨h,ha⟩ => ⟨h.resolve_left ha.ne.symm,ha⟩,fun ⟨h,ha⟩ => ⟨Or.inr h,ha⟩⟩
  rw [hn] at h4
  rw [sum_insert hwH] at h2
  omega

theorem surviving_core (G : SimpleGraph V) (A : Finset V) (d : ℚ)
    (hd : 0 ≤ d)
    (he : (d/4)*Fintype.card V + (1/8:ℚ)*(2*G.edgeFinset.card) <
      ((Density.darts G A).card:ℚ)/2) :
    ∃ S ⊆ A, S.Nonempty ∧ ∀ v ∈ S,
      d/4 ≤ ((S.filter (G.Adj v)).card:ℚ) ∧
      (G.degree v : ℚ)/8 ≤ (S.filter (G.Adj v)).card := by
  classical
  let budget : Finset V → ℚ := fun S =>
    (d/4)*S.card + (1/8:ℚ)*(∑v∈S,(G.degree v:ℚ))
  have hb : 0 ≤ budget A := by dsimp [budget]; positivity
  have hstart : budget A < ((Density.darts G A).card:ℚ)/2 := by
    have hcard : (A.card:ℚ) ≤ Fintype.card V := by exact_mod_cast card_le_univ A
    have hsum : ∑v∈A,(G.degree v:ℚ) ≤ 2*G.edgeFinset.card := by
      calc
        _ ≤ ∑v : V,(G.degree v:ℚ) := sum_le_univ_sum_of_nonneg (fun _ => by positivity)
        _ = _ := by exact_mod_cast G.sum_degrees_eq_twice_card_edges
    dsimp [budget]
    have hc := mul_le_mul_of_nonneg_left hcard (show (0:ℚ)≤d/4 by positivity)
    linarith
  have aux : ∀ n : ℕ, ∀ S ⊆ A, S.card = n → budget S < ((Density.darts G S).card:ℚ)/2 →
      ∃ T ⊆ S, T.Nonempty ∧ ∀ v ∈ T,
        d/4 ≤ ((T.filter (G.Adj v)).card:ℚ) ∧
        (G.degree v : ℚ)/8 ≤ (T.filter (G.Adj v)).card := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hSA hn hs
      by_cases hgood : ∀ v ∈ S, d/4 ≤ ((S.filter (G.Adj v)).card:ℚ) ∧
        (G.degree v : ℚ)/8 ≤ (S.filter (G.Adj v)).card
      · refine ⟨S,Subset.rfl,?_,hgood⟩
        by_contra hne
        have hz : S=∅ := not_nonempty_iff_eq_empty.mp hne
        simp [hz,budget,Density.darts] at hs
      push Not at hgood
      obtain ⟨v,hv,hvbad⟩ := hgood
      have hbdel : budget S = budget (S.erase v) + d/4 + (G.degree v:ℚ)/8 := by
        dsimp [budget]
        rw [←sum_erase_add _ _ hv]
        have hc : (S.card:ℚ) = (S.erase v).card+1 := by exact_mod_cast (card_erase_add_one hv).symm
        rw [hc]
        ring
      have hedel : ((Density.darts G S).card:ℚ)/2 =
          ((Density.darts G (S.erase v)).card:ℚ)/2 + (S.filter (G.Adj v)).card := by
        have hh := Density.darts_erase G hv
        have hh' : ((Density.darts G S).card:ℚ) = (Density.darts G (S.erase v)).card +
          2*(S.filter (G.Adj v)).card := by exact_mod_cast hh
        linarith
      have hvs : ((S.filter (G.Adj v)).card:ℚ) < d/4 + (G.degree v:ℚ)/8 := by
        by_cases hfirst : d/4 ≤ ((S.filter (G.Adj v)).card:ℚ)
        · have hh := hvbad hfirst
          linarith
        · push Not at hfirst
          have : (0:ℚ) ≤ G.degree v := by positivity
          linarith
      have hnew : budget (S.erase v) < ((Density.darts G (S.erase v)).card:ℚ)/2 := by linarith
      obtain ⟨T,hTS,hT,hgoodT⟩ := ih (S.erase v).card (by rw [←hn]; exact card_erase_lt_of_mem hv)
        (S.erase v) (erase_subset _ _ |>.trans hSA) rfl hnew
      exact ⟨T,hTS.trans (erase_subset _ _),hT,hgoodT⟩
  exact aux A.card A Subset.rfl rfl hstart

lemma outside_card_le (G : SimpleGraph V) (H : Finset V) :
    (outside G H).card ≤ ∑ v ∈ H, G.degree v := by
  have hs : outside G H ⊆ H.biUnion (fun v => G.neighborFinset v) := by
    intro w hw
    obtain ⟨_,v,hv,ha⟩ := (mem_outside _ _ _).mp hw
    exact mem_biUnion.mpr ⟨v,hv,by simpa using ha⟩
  exact (card_le_card hs).trans (card_biUnion_le.trans (by simp))

theorem cheap_neighborhood (G : SimpleGraph V) (S X : Finset V) (p : ℕ) (lam M : ℚ)
    (hp : 1 ≤ p) (hlam : 4 ≤ lam) (hM : 0 ≤ M) (hS : S.Nonempty) (hSX : Disjoint S X)
    (hsdeg : ∀ v ∈ S, 25*lam ≤ ((S.filter (G.Adj v)).card:ℚ) ∧
      (G.degree v:ℚ)/8 ≤ (S.filter (G.Adj v)).card)
    (hhigh : ∀ v ∈ S, (G.degree v:ℚ) < M)
    (hXdeg : ∀ v ∈ S, ((X.filter (G.Adj v)).card:ℚ) < lam/4)
    (hnocheap : ∀ H ⊆ S, (G.induce (↑H:Set V)).Connected → H.card=p →
      2*lam*(H.card-1:ℚ) < loss2 G H) :
    ∃ N : Finset V, Disjoint N X ∧ N.Nonempty ∧
      (N.card:ℚ) ≤ p*M ∧ (lam/32)*N.card ≤ (Density.darts G N).card := by
  classical
  let good : Finset (Finset V) := S.powerset.filter fun H => H.Nonempty ∧
    (G.induce (↑H:Set V)).Connected ∧ H.card ≤ p ∧ (loss2 G H:ℚ) ≤ 2*lam*(H.card-1:ℚ)
  obtain ⟨v,hv⟩ := hS
  have hvG : ({v}:Finset V) ∈ good := by
    simp only [good,mem_filter,mem_powerset]
    refine ⟨singleton_subset_iff.mpr hv,by simp,?_,by simpa,by simp⟩
    have he : (↑({v}:Finset V):Set V) = {v} := by ext x; simp
    rw [he]
    exact SimpleGraph.Connected.of_subsingleton
  obtain ⟨H,hHg,hmax⟩ := exists_max_image good card ⟨{v},hvG⟩
  obtain ⟨hHS,hH,hconn,hHp,hcheap⟩ : H ⊆ S ∧ H.Nonempty ∧
      (G.induce (↑H:Set V)).Connected ∧ H.card ≤ p ∧ (loss2 G H:ℚ) ≤ 2*lam*(H.card-1:ℚ) := by
    simpa only [good,mem_filter,mem_powerset,and_assoc] using hHg
  have hplt : H.card < p := lt_of_le_of_ne hHp (fun h => (not_lt_of_ge hcheap) (hnocheap H hHS hconn h))
  let N := outside G H
  have hNS : ∀ w ∈ N ∩ S, lam < 1+((N.filter (G.Adj w)).card:ℚ) := by
    intro w hw
    obtain ⟨hwN,hwS⟩ := mem_inter.mp hw
    by_contra hbad
    push Not at hbad
    have hwH := ((mem_outside _ _ _).mp hwN).1
    obtain ⟨_,u,hu,ha⟩ := (mem_outside _ _ _).mp hwN
    have hnewconn : (G.induce (↑(insert w H):Set V)).Connected := by
      rw [Finset.coe_insert]
      exact Incidence.connected_insert hconn hu ha.symm
    have hnewloss : (loss2 G (insert w H):ℚ) = loss2 G H + 2*(1+(N.filter (G.Adj w)).card) := by
      exact_mod_cast loss2_insert G H hwN
    have hnew : insert w H ∈ good := by
      simp only [good,mem_filter,mem_powerset]
      refine ⟨insert_subset hwS hHS,insert_nonempty _ _,hnewconn,?_,?_⟩
      · rw [card_insert_of_notMem hwH]; omega
      · rw [hnewloss,card_insert_of_notMem hwH]
        push_cast
        nlinarith
    have hh := hmax (insert w H) hnew
    rw [card_insert_of_notMem hwH] at hh
    omega
  let a : ℚ := ∑ v ∈ H, ((S.filter (G.Adj v)).card:ℚ)
  let b : ℚ := ∑ v ∈ H, (G.degree v:ℚ)
  have ha : 25*lam*H.card ≤ a := by
    calc
      _ = ∑ _v ∈ H, 25*lam := by simp [mul_comm]
      _ ≤ a := sum_le_sum (fun v hv => (hsdeg v (hHS hv)).1)
  have hab : b/8 ≤ a := by
    dsimp [a,b]
    rw [sum_div]
    exact sum_le_sum (fun v hv => (hsdeg v (hHS hv)).2)
  have hNb : (N.card:ℚ) ≤ b := by
    dsimp [N,b]
    exact_mod_cast outside_card_le G H
  have haloss : a ≤ (N ∩ S).card + 2*lam*(H.card-1:ℚ) := by
    have hh : a ≤ (S ∩ N).card + (loss2 G H:ℚ) := by
      dsimp [a,N]
      exact_mod_cast restricted_degree_loss G H S hHS
    rw [inter_comm] at hh
    linarith
  have hratio : (N.card:ℚ)/16 ≤ (N ∩ S).card := by nlinarith
  have hNpos : (N ∩ S).Nonempty := by
    have hpH : (0:ℚ) < H.card := by exact_mod_cast card_pos.mpr hH
    have hnpos : (0:ℚ)<(N ∩ S).card := by nlinarith
    exact card_pos.mp (by exact_mod_cast hnpos)
  have hNdeg : ∀ w ∈ N ∩ S, lam/2 ≤ (((N \ X).filter (G.Adj w)).card:ℚ) := by
    intro w hw
    have hh := hNS w hw
    have hx := hXdeg w (mem_inter.mp hw).2
    have hle : (N.filter (G.Adj w)).card ≤ ((N \ X).filter (G.Adj w)).card + (X.filter (G.Adj w)).card := by
      have hsub : N.filter (G.Adj w) ⊆ ((N \ X).filter (G.Adj w)) ∪ X.filter (G.Adj w) := by
        intro z hz
        obtain ⟨hzN,ha⟩ := mem_filter.mp hz
        by_cases hzX : z∈X
        · exact mem_union_right _ (mem_filter.mpr ⟨hzX,ha⟩)
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hzN,hzX⟩,ha⟩)
      exact (card_le_card hsub).trans (card_union_le _ _)
    have hle' : ((N.filter (G.Adj w)).card:ℚ) ≤ ((N \ X).filter (G.Adj w)).card + (X.filter (G.Adj w)).card := by exact_mod_cast hle
    linarith
  have hNSsub : N ∩ S ⊆ N \ X := by
    intro w hw
    exact mem_sdiff.mpr ⟨(mem_inter.mp hw).1,fun hh => disjoint_left.mp hSX (mem_inter.mp hw).2 hh⟩
  refine ⟨N \ X,sdiff_disjoint,hNpos.mono hNSsub,?_,?_⟩
  · have hdeg : b ≤ H.card*M := by
      calc
        _ ≤ ∑ _v ∈ H, M := sum_le_sum (fun v hv => (hhigh v (hHS hv)).le)
        _ = _ := by simp [mul_comm]
    have hpn : (H.card:ℚ)≤p := by exact_mod_cast hHp
    have hcN : ((N \ X).card:ℚ)≤N.card := by exact_mod_cast card_le_card sdiff_subset
    have hmul := mul_le_mul_of_nonneg_right hpn hM
    linarith
  · have hdarts : (lam/2)*(N ∩ S).card ≤ (Density.darts G (N \ X)).card := by
      rw [darts_sum]
      push_cast
      calc
        _ = ∑ _w ∈ N ∩ S, lam/2 := by simp [mul_comm]
        _ ≤ ∑ w ∈ N ∩ S, (((N \ X).filter (G.Adj w)).card:ℚ) := sum_le_sum hNdeg
        _ ≤ ∑ w ∈ N \ X, (((N \ X).filter (G.Adj w)).card:ℚ) :=
          sum_le_sum_of_subset_of_nonneg hNSsub (fun _ _ _ => by positivity)
    have hcard : ((N \ X).card:ℚ) ≤ N.card := by exact_mod_cast card_le_card sdiff_subset
    nlinarith

attribute [instance] CheapMinor.fintype

lemma CheapMinor.exists_minimum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (p : ℕ) (lam : ℚ) :
    ∃ M : CheapMinor G p lam, ∀ N : CheapMinor G p lam, Fintype.card M.W ≤ Fintype.card N.W := by
  have hex : ∃ n : ℕ, ∃ M : CheapMinor G p lam, Fintype.card M.W = n :=
    ⟨Fintype.card V,CheapMinor.initial G p lam,rfl⟩
  obtain ⟨M,hm⟩ := Nat.find_spec hex
  exact ⟨M,fun N => hm ▸ Nat.find_min' hex ⟨N,rfl⟩⟩

lemma CheapMinor.big_card {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) : p*M.big.card ≤ Fintype.card V := by
  classical
  have hh := expand_card G M.graph M.model M.big
  have hs : ∑w∈M.big,(M.model.branch w).toFinset.card = p*M.big.card := by
    calc
      _ = ∑ _w∈M.big,p := sum_congr rfl (fun w hw => (mem_filter.mp hw).2)
      _ = _ := by simp [mul_comm]
  rw [hs] at hh
  exact hh ▸ card_le_univ _

theorem CheapMinor.no_cheap {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) (hp : 2 ≤ p)
    (hmin : ∀ N : CheapMinor G p lam, Fintype.card M.W ≤ Fintype.card N.W)
    (H : Finset M.W) (hc : (M.graph.induce (↑H:Set M.W)).Connected)
    (hcard : H.card=p) (hsmall : ∀ w ∈ H, w ∉ M.big) :
    2*lam*(H.card-1:ℚ) < loss2 M.graph H := by
  by_contra hn
  push Not at hn
  let N := M.contract H hc hcard hsmall hn
  have hh := hmin N
  change Fintype.card M.W ≤ Fintype.card (ContractVertex H) at hh
  rw [contract_card] at hh
  have hcW := card_le_univ H
  omega

lemma kConnected_image {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (f : W → V) (hf : Function.Injective f)
    {S : Finset W} {k : ℕ} (hc : KConnectedOn Q S k)
    (ha : ∀ u ∈ S, ∀ v ∈ S, Q.Adj u v → G.Adj (f u) (f v)) :
    KConnectedOn G (S.image f) k := by
  classical
  refine ⟨by simpa only [card_image_of_injective _ hf] using hc.1,?_⟩
  intro Z hZS hz
  let X := S.filter fun w => f w ∈ Z
  have hXS : X ⊆ S := filter_subset _ _
  have he : X.image f = Z := by
    ext v
    constructor
    · rintro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hw).2
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp (hZS hv)
      exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,hv⟩,rfl⟩
  have hx : X.card < k := by rw [←card_image_of_injective X hf,he]; exact hz
  let g : (Q.induce (↑(S \ X):Set W)) →g (G.induce (↑(S.image f \ Z):Set V)) :=
    { toFun := fun w => ⟨f w.val,mem_sdiff.mpr ⟨mem_image.mpr ⟨w.val,(mem_sdiff.mp w.property).1,rfl⟩,
        fun hz => (mem_sdiff.mp w.property).2 (mem_filter.mpr ⟨(mem_sdiff.mp w.property).1,hz⟩)⟩⟩
      map_rel' := fun {u v} huv => ha u.val (mem_sdiff.mp u.property).1 v.val (mem_sdiff.mp v.property).1 huv }
  apply (hc.2 X hXS hx).map g
  intro v
  obtain ⟨w,hw,heq⟩ := mem_image.mp (mem_sdiff.mp v.property).1
  have hwx : w ∈ S \ X := mem_sdiff.mpr ⟨hw,fun hx =>
    (mem_sdiff.mp v.property).2 (heq ▸ (mem_filter.mp hx).2)⟩
  exact ⟨⟨w,hwx⟩,Subtype.ext heq⟩

lemma CheapMinor.lift_small {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) {S : Finset M.W} {k : ℕ}
    (hc : KConnectedOn M.graph S k) (hsmall : Disjoint S M.big) :
    ∃ T : Finset V, KConnectedOn G T k ∧ T.card = S.card := by
  classical
  let f : M.W → V := fun w => (M.model.connected w).nonempty.some.val
  have hfmem : ∀ w, f w ∈ M.model.branch w := fun w => (M.model.connected w).nonempty.some.property
  have hfi : Function.Injective f := by
    intro a b he
    by_contra hn
    exact Set.disjoint_left.mp (M.model.disjoint a b hn) (hfmem a) (he ▸ hfmem b)
  refine ⟨S.image f,kConnected_image f hfi hc ?_,card_image_of_injective _ hfi⟩
  intro u hu v hv huv
  obtain ⟨a,ha,b,hb,hab⟩ := M.model.adjacent huv
  have he (w : M.W) (hw : w ∈ S) {x : V} (hx : x ∈ M.model.branch w) : x=f w := by
    have hcard := M.small (disjoint_left.mp hsmall hw)
    have hm1 : x ∈ (M.model.branch w).toFinset := Set.mem_toFinset.mpr hx
    have hm2 : f w ∈ (M.model.branch w).toFinset := Set.mem_toFinset.mpr (hfmem w)
    exact (card_le_one.mp hcard.le) x hm1 (f w) hm2
  simpa only [he u hu ha,he v hv hb] using hab

lemma bad_size (R : SimpleGraph V) (X : Finset V) (n q t : ℕ) (d : ℚ)
    (hq : 1 ≤ q) (ht : 1 ≤ t) (hd : 1280800*t < d)
    (hx : q^5*X.card ≤ n) (hupper : (R.edgeFinset.card:ℚ) ≤ d*n)
    (hinc : ∀ A T : Finset V, Disjoint A T →
      (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℚ)) ≤ 4*t*q^2*A.card) :
    (q:ℚ)^3*(badSet R X d q).card ≤ 7*n := by
  classical
  have hqr : (1:ℚ) ≤ q := by exact_mod_cast hq
  have htr : (1:ℚ) ≤ t := by exact_mod_cast ht
  have hdpos : 0<d := by nlinarith
  let Y := Xᶜ.filter fun v => d/400 ≤ ((X.filter (R.Adj v)).card:ℚ)
  let Z := univ.filter fun v => d*q^4 ≤ (R.degree v:ℚ)
  let B := X ∪ Y ∪ Z
  have hyX : Disjoint X Y := disjoint_of_subset_right (filter_subset _ _) disjoint_compl_right
  have hyinc := hinc X Y hyX
  have heY : Y.filter (fun v => 3202*t ≤ (X.filter (R.Adj v)).card) = Y := by
    apply filter_eq_self.mpr
    intro v hv
    have hh := (mem_filter.mp hv).2
    have : (3202*t:ℚ) ≤ (X.filter (R.Adj v)).card := by linarith
    exact_mod_cast this
  rw [heY] at hyinc
  have hylo : (t:ℚ)*Y.card ≤ ∑v∈Y,((X.filter (R.Adj v)).card:ℚ) := by
    calc
      _ = ∑_v∈Y,(t:ℚ) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun v hv => by have hh := (mem_filter.mp hv).2; linarith)
  have hy : (Y.card:ℚ) ≤ 4*q^2*X.card := by nlinarith
  have hzlo : d*q^4*Z.card ≤ ∑v∈Z,(R.degree v:ℚ) := by
    calc
      _ = ∑_v∈Z,d*q^4 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun v hv => (mem_filter.mp hv).2)
  have hzup : (∑v∈Z,(R.degree v:ℚ)) ≤ 2*R.edgeFinset.card := by
    calc
      _ ≤ ∑v : V,(R.degree v:ℚ) := sum_le_univ_sum_of_nonneg (fun _ => by positivity)
      _ = _ := by exact_mod_cast R.sum_degrees_eq_twice_card_edges
  have hz : (q:ℚ)^4*Z.card ≤ 2*n := by nlinarith
  have hxn : (q:ℚ)^5*X.card ≤ n := by exact_mod_cast hx
  have hbn : (B.card:ℚ) ≤ X.card+Y.card+Z.card := by
    exact_mod_cast (card_union_le (X ∪ Y) Z).trans (Nat.add_le_add_right (card_union_le X Y) _)
  have hqpow : (q:ℚ)^3 ≤ (q:ℚ)^4 := pow_le_pow_right₀ hqr (by omega)
  have hqpow2 : (q:ℚ)^3 ≤ (q:ℚ)^5 := by
    exact pow_le_pow_right₀ hqr (by omega)
  have hB : (q:ℚ)^3*B.card ≤ 7*n := by
    have h1 := mul_le_mul_of_nonneg_left hbn (show 0≤(q:ℚ)^3 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hy (show 0≤(q:ℚ)^3 by positivity)
    have h3 := mul_le_mul_of_nonneg_right hqpow (show 0≤(Z.card:ℚ) by positivity)
    have h4 := mul_le_mul_of_nonneg_right hqpow2 (show 0≤(X.card:ℚ) by positivity)
    nlinarith
  exact hB

lemma bad_degree_sum (R : SimpleGraph V) (B : Finset V) (n q t : ℕ)
    (hq : 1 ≤ q) (hn : Fintype.card V ≤ n)
    (hB : (q:ℚ)^3*B.card ≤ 7*n)
    (hcoarse : ∀ A : Finset V, ((Density.darts R A).card:ℚ) ≤ 2*t*q*A.card)
    (hinc : ∀ A T : Finset V, Disjoint A T →
      (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℚ)) ≤ 4*t*q^2*A.card) :
    (∑v∈B,(R.degree v:ℚ)) ≤ 3244*t*n := by
  classical
  have hqr : (1:ℚ)≤q := by exact_mod_cast hq
  have hcross := hinc B Bᶜ disjoint_compl_right
  let U := Bᶜ.filter fun v => 3202*t ≤ (B.filter (R.Adj v)).card
  have hcrossall : (∑v∈Bᶜ,((B.filter (R.Adj v)).card:ℚ)) ≤ 3202*t*n+4*t*q^2*B.card := by
    rw [←sum_filter_add_sum_filter_not Bᶜ (fun v => 3202*t ≤ (B.filter (R.Adj v)).card)]
    have hlo : (∑v∈Bᶜ.filter (fun v => ¬3202*t ≤ (B.filter (R.Adj v)).card),
        ((B.filter (R.Adj v)).card:ℚ)) ≤ 3202*t*n := by
      calc
        _ ≤ ∑_v∈Bᶜ.filter (fun v => ¬3202*t ≤ (B.filter (R.Adj v)).card),(3202*t:ℚ) :=
          sum_le_sum (fun v hv => by exact_mod_cast (le_of_lt (not_le.mp (mem_filter.mp hv).2)))
        _ = (3202*t:ℚ)*(Bᶜ.filter (fun v => ¬3202*t ≤ (B.filter (R.Adj v)).card)).card := by simp [mul_comm]
        _ ≤ 3202*t*n := by gcongr; exact_mod_cast (card_le_univ _).trans hn
    linarith
  have hds : (∑v∈B,(R.degree v:ℚ)) = (Density.darts R B).card +
      ∑v∈Bᶜ,((B.filter (R.Adj v)).card:ℚ) := by
    have he : ∑v∈B,R.degree v = (Density.darts R B).card + ∑v∈Bᶜ,(B.filter (R.Adj v)).card := by
      simp only [degree_partition R B,sum_add_distrib,darts_sum,degree_sum_comm]
    exact_mod_cast he
  have hq1 : (q:ℚ) ≤ (q:ℚ)^3 := by simpa only [pow_one] using (pow_le_pow_right₀ hqr (show 1≤3 by omega))
  have hq2 : (q:ℚ)^2 ≤ (q:ℚ)^3 := pow_le_pow_right₀ hqr (by omega)
  have hdegB : (∑v∈B,(R.degree v:ℚ)) ≤ 3244*t*n := by
    have hc := hcoarse B
    have h1 := mul_le_mul_of_nonneg_right hq1 (show 0≤(B.card:ℚ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hq2 (show 0≤(B.card:ℚ) by positivity)
    have h3 : (q:ℚ)*B.card ≤ 7*n := h1.trans hB
    have h4 : (q:ℚ)^2*B.card ≤ 7*n := h2.trans hB
    have h5 := mul_le_mul_of_nonneg_left h3 (show 0≤2*(t:ℚ) by positivity)
    have h6 := mul_le_mul_of_nonneg_left h4 (show 0≤4*(t:ℚ) by positivity)
    nlinarith
  exact hdegB

theorem bad_set_core (R : SimpleGraph V) (X : Finset V) (n q t : ℕ) (d : ℚ)
    (hq : 1 ≤ q) (ht : 1 ≤ t) (hd : 1280800*t < d)
    (hnposNat : 0 < n) (hn : Fintype.card V ≤ n) (hx : q^5*X.card ≤ n)
    (hupper : (R.edgeFinset.card:ℚ) ≤ d*n)
    (hlower : (99/100:ℚ)*d*n ≤ R.edgeFinset.card)
    (hcoarse : ∀ A : Finset V, ((Density.darts R A).card:ℚ) ≤ 2*t*q*A.card)
    (hinc : ∀ A T : Finset V, Disjoint A T →
      (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℚ)) ≤ 4*t*q^2*A.card) :
    ∃ S : Finset V, S.Nonempty ∧ Disjoint S X ∧
      (∀ v ∈ S, d/4 ≤ ((S.filter (R.Adj v)).card:ℚ) ∧
        (R.degree v:ℚ)/8 ≤ (S.filter (R.Adj v)).card) ∧
      (∀ v ∈ S, (R.degree v:ℚ) < d*q^4) ∧
      (∀ v ∈ S, ((X.filter (R.Adj v)).card:ℚ) < d/400) := by
  classical
  have hqr : (1:ℚ)≤q := by exact_mod_cast hq
  have htr : (1:ℚ)≤t := by exact_mod_cast ht
  have hdpos : 0<d := by nlinarith
  let B := badSet R X d q
  have hB := bad_size R X n q t d hq ht hd hx hupper hinc
  have hdegB := bad_degree_sum R B n q t hq hn hB hcoarse hinc
  have hnpos : (0:ℚ)<n := by exact_mod_cast hnposNat
  have hremain : (d/4)*Fintype.card V+(1/8:ℚ)*(2*R.edgeFinset.card) <
      ((Density.darts R Bᶜ).card:ℚ)/2 := by
    have hpart : 2*(R.edgeFinset.card:ℚ)+(Density.darts R B).card =
        (Density.darts R Bᶜ).card+2*∑v∈B,(R.degree v:ℚ) := by exact_mod_cast darts_partition R B
    have hnn : (Fintype.card V:ℚ) ≤ n := by exact_mod_cast hn
    have hdnt := mul_lt_mul_of_pos_right hd hnpos
    have hdnn := mul_le_mul_of_nonneg_left hnn hdpos.le
    have hdn := mul_le_mul_of_nonneg_left hupper (by norm_num : (0:ℚ)≤1/4)
    have hnn2 := mul_le_mul_of_nonneg_left hdnn (by norm_num : (0:ℚ)≤1/4)
    have hdarts : (0:ℚ)≤(Density.darts R B).card := by positivity
    linarith
  obtain ⟨S,hS,hSn,hSd⟩ := surviving_core R Bᶜ d hdpos.le hremain
  have hnot (v : V) (hv : v∈S) : v∉B := mem_compl.mp (hS hv)
  refine ⟨S,hSn,?_,hSd,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hx
    exact hnot v hv (mem_union_left _ (mem_union_left _ hx))
  · intro v hv
    by_contra hh
    exact hnot v hv (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,le_of_not_gt hh⟩))
  · intro v hv
    by_contra hh
    have hvX : v∉X := fun hx => hnot v hv (mem_union_left _ (mem_union_left _ hx))
    exact hnot v hv (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_compl.mpr hvX,le_of_not_gt hh⟩)))

theorem district_finite (G : SimpleGraph V) [Nonempty V] (q t k : ℕ)
    (hq : 2 ≤ q) (ht : 1 ≤ t) (hk : 1 ≤ k)
    (hd : max (1280800*t:ℚ) (12800*k) < Knitting.density G)
    (hcoarse : ∀ (W : Type) [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      MinorModel G R → ∀ A : Finset W, ((Density.darts R A).card:ℚ) ≤ 2*t*q*A.card)
    (hinc : ∀ (W : Type) [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      MinorModel G R → ∀ A T : Finset W, Disjoint A T →
      (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℚ)) ≤ 4*t*q^2*A.card) :
    ∃ S : Finset V, KConnectedOn G S k ∧
      (S.card:ℚ) ≤ Knitting.density G*q^9 := by
  classical
  let d := Knitting.density G
  let lam := d/100
  obtain ⟨M,hmin⟩ := CheapMinor.exists_minimum G (q^5) lam
  have hp : 2≤q^5 := by
    have hh : q ≤ q^5 := by simpa only [pow_one] using (Nat.pow_le_pow_right (by omega : 0<q) (show 1≤5 by omega))
    omega
  have hd1 : (1280800*t:ℚ)<d := (le_max_left _ _).trans_lt hd
  have hd2 : (12800*k:ℚ)<d := (le_max_right _ _).trans_lt hd
  have htr : (1:ℚ)≤t := by exact_mod_cast ht
  have hkr : (1:ℚ)≤k := by exact_mod_cast hk
  have hdpos : 0<d := by nlinarith
  have heq : d*Fintype.card V = G.edgeFinset.card := Knitting.density_mul_order G Fintype.card_pos
  have hup : (M.graph.edgeFinset.card:ℚ) ≤ d*Fintype.card V := by
    rw [heq]; exact_mod_cast M.upper
  have hlo : (99/100:ℚ)*d*Fintype.card V ≤ M.graph.edgeFinset.card := by
    have hh := M.budget
    have ho : (0:ℚ)≤Fintype.card M.W := by positivity
    have hh' : lam*Fintype.card M.W ≥ 0 := by dsimp [lam]; positivity
    dsimp [lam] at hh hh'
    rw [←heq] at hh
    linarith
  obtain ⟨S,hSn,hSX,hSd,hhigh,hXdeg⟩ := bad_set_core M.graph M.big
    (Fintype.card V) q t d (by omega) ht hd1 Fintype.card_pos
    (Knitting.model_card_le M.model) M.big_card hup hlo
    (hcoarse _ M.graph M.model) (hinc _ M.graph M.model)
  have hnocheap : ∀ H ⊆ S, (M.graph.induce (↑H:Set M.W)).Connected → H.card=q^5 →
      2*lam*(H.card-1:ℚ) < loss2 M.graph H := by
    intro H hHS hc hcard
    exact M.no_cheap hp hmin H hc hcard (fun w hw => disjoint_left.mp hSX (hHS hw))
  obtain ⟨N,hNX,hNn,hNcard,hNden⟩ := cheap_neighborhood M.graph S M.big (q^5) lam (d*q^4)
    (by omega) (by dsimp [lam]; linarith) (by positivity) hSn hSX
    (fun v hv => by obtain ⟨ha,hb⟩ := hSd v hv; exact ⟨by dsimp [lam]; linarith,hb⟩)
    hhigh (fun v hv => by have hh := hXdeg v hv; dsimp [lam]; linarith) hnocheap
  have hNpos : (0:ℚ)<N.card := by exact_mod_cast card_pos.mpr hNn
  have hNedges : 4*k*N.card < (Density.darts M.graph N).card := by
    have hh := mul_lt_mul_of_pos_right hd2 hNpos
    have hden : (d/3200)*N.card ≤ (Density.darts M.graph N).card := by
      dsimp [lam] at hNden; linarith
    have : (4*(k:ℚ)*N.card) < (Density.darts M.graph N).card := by linarith
    exact_mod_cast this
  obtain ⟨T,hTN,hTc⟩ := Density.connectivity_of_density M.graph N hk hNedges
  obtain ⟨U,hUc,hUcard⟩ := M.lift_small hTc (disjoint_of_subset_left hTN hNX)
  refine ⟨U,hUc,?_⟩
  calc
    (U.card:ℚ) = T.card := by exact_mod_cast hUcard
    _ ≤ N.card := by exact_mod_cast card_le_card hTN
    _ ≤ (q^5:ℕ)*(d*q^4) := hNcard
    _ = d*q^9 := by push_cast; ring

lemma darts_induce (G : SimpleGraph V) (A : Finset V) :
    (Density.darts G A).card = 2*(G.induce (↑A:Set V)).edgeFinset.card := by
  classical
  rw [darts_sum,←SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp only [CoarseDensity.degree_induce_finset]
  exact (Finset.sum_coe_sort A (fun v => (A.filter (G.Adj v)).card)).symm

lemma coarse_darts (G : SimpleGraph V) {q t : ℕ} (ht : 2≤t)
    (hex : hadwigerNumber G<t) (hl : 100000000*Real.log (2*t) ≤ (q:ℝ))
    (A : Finset V) : ((Density.darts G A).card:ℚ) ≤ 2*t*q*A.card := by
  classical
  let H := G.induce (↑A:Set V)
  have hi := (Knitting.model_induce G A).hadwiger_le.trans_lt hex
  have hd := CoarseDensity.density_bound H ht hi
  have hdq : ((Knitting.density H:ℚ):ℝ) ≤ (t:ℝ)*q := by
    calc
      _ ≤ 100000000*t*Real.log (2*t) := hd
      _ = (t:ℝ)*(100000000*Real.log (2*t)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  by_cases hA : A.Nonempty
  · have hn : 0<Fintype.card (↑A:Set V) := by simpa using card_pos.mpr hA
    have he := Knitting.density_mul_order H hn
    have he' : ((Knitting.density H:ℚ):ℝ)*A.card = H.edgeFinset.card := by
      have hr := congrArg (fun x : ℚ => (x:ℝ)) he
      convert hr using 1 <;> simp
      congr 1
    have hh := mul_le_mul_of_nonneg_right hdq (show (0:ℝ)≤A.card by positivity)
    rw [he'] at hh
    rw [darts_induce]
    have : (2*(H.edgeFinset.card:ℝ)) ≤ 2*t*q*A.card := by linarith
    exact_mod_cast this
  · have he : A=∅ := not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [Density.darts]

open Filter Real Asymptotics in
lemma district_cutoff : ∀ᶠ z : ℝ in atTop,
    2 ≤ z ∧ 2 ≤ z^(1/200:ℝ) ∧ 1024 ≤ z^(1/100:ℝ) ∧
      100000000*Real.log (2*z) ≤ z^(1/200:ℝ) := by
  have h1 := (tendsto_atTop.mp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/200))) 2
  have h2 := (tendsto_atTop.mp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100))) 1024
  filter_upwards [Incidence.incidence_cutoff,h1,h2] with z hz hz1 hz2
  exact ⟨hz.1,hz1,hz2,hz.2.2.2.2⟩

lemma district_order {t q : ℕ} (ht : (2:ℝ)≤t)
    (hq : (q:ℝ)≤2*(t:ℝ)^(1/200:ℝ))
    (hpow : (1024:ℝ)≤(t:ℝ)^(1/100:ℝ)) :
    (t:ℝ)*q^10 ≤ (t:ℝ)^(53/50:ℝ) := by
  have htpos : (0:ℝ)<t := by linarith
  have he : (t:ℝ)*((t:ℝ)^(1/200:ℝ))^10 = (t:ℝ)^(21/20:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul htpos.le]
    calc
      _ = (t:ℝ)^(1:ℝ)*(t:ℝ)^((1/200:ℝ)*(10:ℝ)) := by norm_num
      _ = _ := by rw [←Real.rpow_add htpos]; norm_num
  have hp := pow_le_pow_left₀ (show (0:ℝ)≤q by positivity) hq 10
  calc
    _ ≤ (t:ℝ)*(2*(t:ℝ)^(1/200:ℝ))^10 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 1024*((t:ℝ)*((t:ℝ)^(1/200:ℝ))^10) := by ring
    _ = 1024*(t:ℝ)^(21/20:ℝ) := by rw [he]
    _ ≤ (t:ℝ)^(1/100:ℝ)*(t:ℝ)^(21/20:ℝ) := by gcongr
    _ = _ := by rw [←Real.rpow_add htpos]; norm_num

theorem district : Statement := by
  classical
  intro K hK
  let D := max 1280800 (12800*K)+1
  refine ⟨D,by dsimp [D]; norm_num,?_⟩
  obtain ⟨t₁,ht₁⟩ := Incidence.incidence_bound
  obtain ⟨t₂,ht₂⟩ := Filter.eventually_atTop.mp district_cutoff.natCast_atTop
  refine ⟨max t₁ t₂,?_⟩
  intro t htt W _ _ _ P hex hedges
  obtain ⟨htr,hpow2,hpow1024,hlog⟩ := ht₂ t (le_trans (le_max_right _ _) htt)
  have ht : 2≤t := by exact_mod_cast htr
  have htpos : (0:ℝ)<t := by linarith
  let q := Nat.ceil ((t:ℝ)^(1/200:ℝ))
  have hqlo : (t:ℝ)^(1/200:ℝ) ≤ q := Nat.le_ceil _
  have hq : 2≤q := by exact_mod_cast hpow2.trans hqlo
  have hqhi : (q:ℝ)≤2*(t:ℝ)^(1/200:ℝ) := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg htpos.le (1/200:ℝ))
    change (q:ℝ)<(t:ℝ)^(1/200:ℝ)+1 at hh
    linarith
  have hlogq : 100000000*Real.log (2*t) ≤ (q:ℝ) := hlog.trans hqlo
  have hdense : (D*t:ℚ) ≤ Knitting.density P := by
    have hn : (0:ℚ)<Fintype.card W := by exact_mod_cast Fintype.card_pos
    apply (le_div_iff₀ hn).mpr
    exact_mod_cast hedges
  have hD1 : (1280800:ℚ)<D := by exact_mod_cast (show 1280800<D by dsimp [D]; omega)
  have hD2 : (12800*K:ℚ)<D := by exact_mod_cast (show 12800*K<D by dsimp [D]; omega)
  have htq : (0:ℚ)<t := by exact_mod_cast (show 0<t by omega)
  have hden : max (1280800*t:ℚ) (12800*(K*t)) < Knitting.density P := by
    apply max_lt
    · exact (mul_lt_mul_of_pos_right hD1 htq).trans_le hdense
    · have hh := mul_lt_mul_of_pos_right hD2 htq
      nlinarith
  have hpowinc : (t:ℝ)^(101/100:ℝ) ≤ 4*t*q^2 := by
    have he : (t:ℝ)^(101/100:ℝ) = (t:ℝ)*((t:ℝ)^(1/200:ℝ))^2 := by
      rw [←Real.rpow_natCast,←Real.rpow_mul htpos.le]
      calc
        _ = (t:ℝ)^((1:ℝ)+(1/200:ℝ)*2) := by norm_num
        _ = _ := by rw [Real.rpow_add htpos,Real.rpow_one]; norm_num
    rw [he]
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg htpos.le _) hqlo 2
    have hx := mul_le_mul_of_nonneg_left hh htpos.le
    nlinarith [sq_nonneg (q:ℝ)]
  obtain ⟨S,hSc,hScard⟩ := district_finite P q t (K*t) hq (by omega) (by nlinarith) (by simpa only [Nat.cast_mul] using hden)
    (fun U _ _ R M A => coarse_darts R ht (M.hadwiger_le.trans_lt hex) hlogq A)
    (by
      intro U _ _ R M A T hdis
      have hh := ht₁ t (le_trans (le_max_left _ _) htt) U R
        (M.hadwiger_le.trans_lt hex) A T hdis
      have hp := mul_le_mul_of_nonneg_right hpowinc (show (0:ℝ)≤A.card by positivity)
      have hbound : (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℝ)) ≤ 4*t*q^2*A.card := hh.trans hp
      exact_mod_cast hbound)
  refine ⟨S,hSc,?_⟩
  have hd := CoarseDensity.density_bound P ht hex
  have hdq : ((Knitting.density P:ℚ):ℝ) ≤ (t:ℝ)*q := by
    have hh := mul_le_mul_of_nonneg_left hlogq htpos.le
    nlinarith
  have hcard : (S.card:ℝ) ≤ ((Knitting.density P:ℚ):ℝ)*q^9 := by exact_mod_cast hScard
  have hm := mul_le_mul_of_nonneg_right hdq (show (0:ℝ)≤(q:ℝ)^9 by positivity)
  calc
    _ ≤ ((Knitting.density P:ℚ):ℝ)*q^9 := hcard
    _ ≤ (t:ℝ)*q*q^9 := hm
    _ = (t:ℝ)*q^10 := by ring
    _ ≤ _ := district_order htr hqhi hpow1024

end
end LinearListHadwiger.District

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.DistrictAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.District
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma list_dense_core (G : SimpleGraph V) {d : ℕ}
    (hl : d+1 < listChromaticNumber G) :
    ∃ S : Finset V, S.Nonempty ∧
      (d+1)*S.card ≤ 2*(G.induce (↑S:Set V)).edgeFinset.card := by
  classical
  have hnot : ¬DegenerateOn G univ d := by
    intro h
    exact (not_le_of_gt hl) (listChromaticNumber_le_of_degenerate G h)
  have hx : ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, d < (S.filter (G.Adj v)).card := by
    by_contra hn
    apply hnot
    intro S _ hS
    by_contra hh
    apply hn
    refine ⟨S,hS,?_⟩
    intro v hv
    by_contra hn
    exact hh ⟨v,hv,by omega⟩
  obtain ⟨S,hS,hdeg⟩ := hx
  refine ⟨S,hS,?_⟩
  rw [←darts_induce,darts_sum]
  calc
    (d+1)*S.card = ∑ v ∈ S, (d+1) := by simp [mul_comm]
    _ ≤ _ := sum_le_sum fun v hv => by have := hdeg v hv; omega

theorem list_district : ∀ K : ℕ, 0 < K → ∃ D : ℕ,
    max (400*3202) (12800*K) < D ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (P : SimpleGraph W),
    hadwigerNumber P < t → 2*D*t+2 < listChromaticNumber P →
    ∃ S : Finset W, KConnectedOn P S (K*t) ∧
      (S.card : ℝ) ≤ (t:ℝ)^(53/50:ℝ) := by
  intro K hK
  obtain ⟨D,hD,t₀,hd⟩ := district K hK
  refine ⟨D,hD,t₀,?_⟩
  intro t ht W _ _ P hex hl
  obtain ⟨A,hA,hden⟩ := list_dense_core P (d := 2*D*t+1) (by omega)
  let : Nonempty (↑A:Set W) := ⟨⟨hA.choose,hA.choose_spec⟩⟩
  have hh := (Knitting.model_induce P A).hadwiger_le.trans_lt hex
  have he : D*t*Fintype.card (↑A:Set W) ≤ (P.induce (↑A:Set W)).edgeFinset.card := by
    have hAc : Fintype.card (↑A:Set W) = A.card := by simp
    rw [hAc]
    nlinarith
  obtain ⟨S,hSc,hcard⟩ := hd t ht (↑A:Set W) (P.induce (↑A:Set W)) hh he
  refine ⟨S.image Subtype.val,kConnected_image Subtype.val Subtype.val_injective hSc
    (fun _ _ _ _ h => h),?_⟩
  simpa only [card_image_of_injective _ Subtype.val_injective] using hcard

end
end LinearListHadwiger.District

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.SamplingConnectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Knitting
open Finset
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

lemma kConnected_image {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] (G : SimpleGraph V) (f : W → V) (hf : Function.Injective f)
    {T : Finset W} {k : ℕ} (hc : KConnectedOn (G.comap f) T k) :
    KConnectedOn G (T.image f) k := by
  classical
  refine ⟨by simpa only [card_image_of_injective _ hf] using hc.1,?_⟩
  intro X hX hx
  let Y := T.filter (fun w => f w∈X)
  have hYT : Y ⊆ T := filter_subset _ _
  have hYX : Y.image f=X := by
    ext v
    constructor
    · rintro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hw).2
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp (hX hv)
      exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,hv⟩,rfl⟩
  have hYc : Y.card=X.card := by rw [←hYX,card_image_of_injective _ hf]
  have hcon := hc.2 Y hYT (hYc ▸ hx)
  let g : (G.comap f).induce (↑(T\Y) : Set W) →g
      G.induce (↑(T.image f\X) : Set V) :=
    { toFun := fun w => ⟨f w.val,mem_sdiff.mpr
        ⟨mem_image.mpr ⟨w.val,(mem_sdiff.mp w.property).1,rfl⟩,by
          intro h
          exact (mem_sdiff.mp w.property).2
            (mem_filter.mpr ⟨(mem_sdiff.mp w.property).1,h⟩)⟩⟩
      map_rel' := by intro u v h; exact h }
  apply hcon.map g
  intro v
  obtain ⟨w,hw,he⟩ := mem_image.mp (mem_sdiff.mp v.property).1
  have hwY : w∉Y := by
    intro hh
    exact (mem_sdiff.mp v.property).2 (he ▸ (mem_filter.mp hh).2)
  exact ⟨⟨w,mem_sdiff.mpr ⟨hw,hwY⟩⟩,Subtype.ext he⟩

end LinearListHadwiger.Knitting

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.SmallList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.SmallList
open Finset Fractional
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma number_iso {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : number G=number H := by
  apply le_antisymm
  · have he : G=H.comap e := by ext u v; exact e.map_adj_iff.symm
    rw [he]
    exact number_comap H e
  · have he : H=G.comap e.symm := by ext u v; exact e.symm.map_adj_iff.symm
    rw [he]
    exact number_comap G e.symm

omit [Fintype V] in
lemma obstruction_induce (G : SimpleGraph V) (R : Finset V)
    (h : FractionalObstruction (G.induce (↑R:Set V))) : FractionalObstruction G := by
  obtain ⟨A,hA⟩ := h
  let e := induceImageIso G R A
  have hm := (singletonModel _ _ e.symm e.symm.injective
    (fun {_ _} ha => e.symm.map_adj_iff.mpr ha)).hadwiger_le
  refine ⟨A.image Subtype.val,?_⟩
  rw [number_iso e] at hA
  have hm' : (hadwigerNumber (G.induce (↑(A.image Subtype.val):Set V)):ℝ) ≤
      hadwigerNumber ((G.induce (↑R:Set V)).induce (↑A:Set (↑R:Set V))) := by
    exact_mod_cast hm
  linarith

end LinearListHadwiger.SmallList

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Stage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open Finset
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
lemma list_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    listChromaticNumber G = listChromaticNumber H := by
  apply le_antisymm
  · exact (listChromaticNumber_le_iff _ _).mpr
      (choosable_of_iso e (choosable_listChromaticNumber H))
  · exact (listChromaticNumber_le_iff _ _).mpr
      (choosable_of_iso e.symm (choosable_listChromaticNumber G))

omit [Fintype W] [Fintype V] [DecidableEq W] in
lemma ell_image (G : SimpleGraph V) (f : W → V) (hf : Function.Injective f) (T : Finset W) :
    ell (G.comap f) T = ell G (T.image f) := by
  let e : (G.comap f).induce (↑T : Set W) ≃g G.induce (↑(T.image f) : Set V) :=
    { toEquiv := (Equiv.Set.image f (↑T : Set W) hf).trans
        (Equiv.setCongr (by exact (Finset.coe_image).symm))
      map_rel_iff' := by intro a b; rfl }
  exact list_iso e

theorem districts_on : ∀ K : ℕ, 0<K → ∃ D : ℕ,
    max (400*3202) (12800*K)<D ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀≤t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V),
    hadwigerNumber G<t → 2*D*t+2<ell G S →
    ∃ J⊆S, KConnectedOn G J (K*t) ∧ (J.card:ℝ)≤(t:ℝ)^(53/50:ℝ) := by
  intro K hK
  obtain ⟨D,hD,T,hT⟩ := District.list_district K hK
  refine ⟨D,hD,T,?_⟩
  intro t ht V _ _ G S hminor hl
  obtain ⟨J,hJc,hJs⟩ := hT t ht (↑S:Set V) (G.induce (↑S:Set V))
    ((Knitting.model_induce G S).hadwiger_le.trans_lt hminor) hl
  refine ⟨J.image Subtype.val,by rintro v hv; obtain ⟨w,hw,rfl⟩ := mem_image.mp hv; exact w.property,
    Knitting.kConnected_image G Subtype.val Subtype.val_injective hJc,?_⟩
  simpa only [card_image_of_injective _ Subtype.val_injective] using hJs

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset SmallList
attribute [local instance] Classical.propDecidable

theorem small_set_loss_on : ∃ T : ℕ, ∀ t : ℕ, T≤t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S X : Finset V),
    hadwigerNumber G<t → (X.card:ℝ)≤(t:ℝ)^(53/50:ℝ) →
    ell G S ≤ ell G (S\X)+(4*32768+5)*t ∨ FractionalObstruction G := by
  classical
  obtain ⟨T,hT⟩ := additive_deletion_or_obstruction
  refine ⟨max 1 T,?_⟩
  intro t ht V _ _ G S X hminor hXs
  have ht1 : 1≤t := (le_max_left _ _).trans ht
  let Y : Finset (↑S:Set V) := univ.filter (fun v => v.val∈X)
  have hY : Y.card≤X.card := by
    rw [←card_image_of_injective Y Subtype.val_injective]
    apply card_le_card
    rintro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp hw).2
  have hsize : (Y.card:ℝ)≤(t:ℝ)^(11/10:ℝ) := by
    apply (by exact_mod_cast hY : (Y.card:ℝ)≤X.card).trans
    apply hXs.trans
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast ht1) (by norm_num)
  have he : (univ\(Y∪∅)).image Subtype.val=S\X := by
    ext v
    simp only [union_empty,mem_image,mem_sdiff,mem_univ,mem_filter,true_and,Y]
    constructor
    · rintro ⟨w,hw,rfl⟩; exact ⟨w.property,hw⟩
    · rintro ⟨hv,hx⟩; exact ⟨⟨v,hv⟩,hx,rfl⟩
  rcases hT t ((le_max_right _ _).trans ht) (↑S:Set V) (G.induce (↑S:Set V)) Y ∅ 0
    ((Knitting.model_induce G S).hadwiger_le.trans_lt hminor) hsize (by simp)
    (by intro A hA hAn; have ha : A=∅ := subset_empty.mp hA; simp [ha] at hAn)
    (by simp) with hl|hb
  · left
    have hz := ell_image G (Subtype.val : (↑S:Set V)→V) Subtype.val_injective (univ\(Y∪∅))
    rw [he] at hz
    change ell (G.induce (↑S:Set V)) (univ\(Y∪∅)) = _ at hz
    change ell G S ≤ ell (G.induce (↑S:Set V)) (univ\(Y∪∅))+(4*32768+0+5)*t at hl
    simpa only [hz,Nat.add_zero] using hl
  · exact Or.inr (obstruction_induce G S hb)

theorem two_districts_oai : ∀ K : ℕ, 0<K → ∃ D : ℕ,
    max (400*3202) (12800*K)<D ∧ ∃ T : ℕ, ∀ t : ℕ, T≤t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V),
    hadwigerNumber G<t → (2*D+4*32768+5)*t+2<ell G S →
    (∃ J⊆S, ∃ H⊆S, Disjoint J H ∧ KConnectedOn G J (K*t) ∧
      KConnectedOn G H (K*t) ∧ (J.card:ℝ)≤(t:ℝ)^(53/50:ℝ) ∧
      (H.card:ℝ)≤(t:ℝ)^(53/50:ℝ)) ∨ FractionalObstruction G := by
  intro K hK
  obtain ⟨D,hD,T,hT⟩ := districts_on K hK
  obtain ⟨T',hT'⟩ := small_set_loss_on
  refine ⟨D,hD,max T T',?_⟩
  intro t ht V _ _ G S hminor hl
  obtain ⟨J,hJS,hJc,hJsize⟩ := hT t ((le_max_left _ _).trans ht) V G S hminor (by nlinarith)
  rcases hT' t ((le_max_right _ _).trans ht) V G S J hminor hJsize with hloss|hbad
  · obtain ⟨H,hHS,hHc,hHsize⟩ := hT t ((le_max_left _ _).trans ht) V G (S\J) hminor (by nlinarith)
    exact Or.inl ⟨J,hJS,H,hHS.trans sdiff_subset,
      Finset.disjoint_left.mpr (fun v hvJ hvH => (mem_sdiff.mp (hHS hvH)).2 hvJ),hJc,hHc,hJsize,hHsize⟩
  · exact Or.inr hbad

end LinearListHadwiger.Stage

end OAI
end

theorem solution : type_of% @OAI.LinearListHadwiger.Stage.two_districts_oai := @OAI.LinearListHadwiger.Stage.two_districts_oai
