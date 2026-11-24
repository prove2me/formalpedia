-- Prove2me | solution 1 for GlobalTheory.KeyKa.KoszulTors.koszul_tors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:20:25.165211+00:00
-- url     : https://prove2.me/submissions/750ee3cd-5e1d-4cbd-85ae-eb163c975f3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsUnitField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsCxOfFactor
import Theorems.Thm_GlobalTheory_TorsExists_exists_torsSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa.KoszulTors
section Alg
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
end Alg
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ} in
private lemma kosD_inl_indep_ev
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev ev' : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (p : (I : Finset (Fin g)) × Fin (N I.card)) (y : _root_.GlobalTheory.KeyKa.KIx g d N) :
    _root_.GlobalTheory.KeyKa.kosD m ev (.inl p) y = _root_.GlobalTheory.KeyKa.kosD m ev' (.inl p) y := by
  rcases y with q | b <;> rfl
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ} in
private lemma kosD_inr_eq_zero
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (x : _root_.GlobalTheory.KeyKa.KIx g d N) (a : Fin d) :
    _root_.GlobalTheory.KeyKa.kosD m ev x (.inr a) = 0 := by
  rcases x with p | b <;> rfl
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ} in
private lemma map_kosD_inl_inl {S : Type} [CommRing S] (f : R →+* S)
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    {d' : ℕ} (e : ∀ j, Matrix (Fin d') (Fin (N j)) S) (p q : (I : Finset (Fin g)) × Fin (N I.card)) :
    f (_root_.GlobalTheory.KeyKa.kosD m ev (.inl p) (.inl q)) =
      _root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map f) e (.inl p) (.inl q) := by
  simp [_root_.GlobalTheory.KeyKa.kosD, map_sum, apply_ite]
end GlobalTheory.KeyKa.KoszulTors
end

set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KoszulTors
namespace GlobalTheory.KeyKa.KoszulTors
namespace _root_.GlobalTheory.KeyKa.KoszulTors
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O]
    (g d : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O)
    (ev ev₀ : ∀ j, Matrix (Fin d) (Fin (N j)) O) (Pm : Matrix (Fin d) (Fin d) O),
    _root_.GlobalTheory.KeyKa.IsCx _root_.GlobalTheory.KeyKa.kdeg (_root_.GlobalTheory.KeyKa.kosD m ev) →
    ev 0 = Pm * ev₀ 0 → Pm.det ≠ 0 → Function.Surjective (ev₀ 0).mulVec →
    (∀ v, (ev 0).mulVec v = 0 → ∃ w : Fin g → Fin (N 1) → O, v = ∑ i, (m i 0 1).mulVec (w i)) →
    (∀ v : _root_.GlobalTheory.KeyKa.KIx g 0 N → IsLocalRing.ResidueField O,
      (_root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O))
        (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (_root_.GlobalTheory.KeyKa.kosD (d := 0)
        (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p)) →
    _root_.GlobalTheory.KeyKa.IsCx _root_.GlobalTheory.KeyKa.kdeg (_root_.GlobalTheory.KeyKa.kosD m ev₀) ∧
      ∃ t, _root_.GlobalTheory.KeyKa.TorsSq _root_.GlobalTheory.KeyKa.kdeg
        (_root_.GlobalTheory.KeyKa.kosD m ev₀) t := by
  intro O _ _ _ g d N m ev ev₀ Pm hcx hev hdet hsurj hker hres
  set K := _root_.GlobalTheory.KeyKa.kosD m ev with hK
  set K₀ := _root_.GlobalTheory.KeyKa.kosD m ev₀ with hK₀
  have hrow : ∀ p y, K (.inl p) y = K₀ (.inl p) y := fun p y =>
    kosD_inl_indep_ev m ev ev₀ p y
  have haug : ∀ a y, K (.inr a) y = ∑ b, Pm a b * K₀ (.inr b) y := by
    intro a y
    rcases y with ⟨I, l⟩ | c
    · by_cases hI : I = ∅
      · subst hI
        show ev 0 a l = ∑ b, Pm a b * (if (∅ : Finset (Fin g)) = ∅ then ev₀ 0 b l else 0)
        rw [hev]
        exact Matrix.mul_apply.trans (Finset.sum_congr rfl fun b _ => by rw [if_pos rfl])
      · show (if I = ∅ then ev I.card a l else 0) = ∑ b, Pm a b * (if I = ∅ then ev₀ I.card b l else 0)
        simp [hI]
    · simp [hK, hK₀, kosD_inr_eq_zero]
  have hcx₀ : _root_.GlobalTheory.KeyKa.IsCx _root_.GlobalTheory.KeyKa.kdeg K₀ := by
    refine ⟨fun x y hxy => ?_, ?_⟩
    · rcases x with p | a
      · rw [← hrow]; exact hcx.1 _ _ hxy
      · rcases y with ⟨I, l⟩ | c
        · have hI : I ≠ ∅ := by
            rintro rfl
            exact hxy rfl
          show (if I = ∅ then ev₀ I.card a l else 0) = 0
          simp [hI]
        · exact kosD_inr_eq_zero m ev₀ _ c
    · have hsq : ∀ x y, ∑ b, K x b * K b y = 0 := fun x y => by
        have := congrFun (congrFun hcx.2 x) y
        simpa [Matrix.mul_apply] using this
      ext x y
      rw [Matrix.mul_apply, Matrix.zero_apply]
      have hmid : ∀ x b, K₀ x b * K₀ b y = K₀ x b * K b y := by
        intro x b
        rcases b with q | c
        · rw [hrow]
        · have hz : K₀ x (.inr c) = 0 := kosD_inr_eq_zero m ev₀ x c
          rw [hz, zero_mul, zero_mul]
      rcases x with p | a
      · rw [← hsq (.inl p) y]
        refine Fintype.sum_congr _ _ fun b => ?_
        rw [hmid, hrow]
      · have hvec : Pm.mulVec (fun b => ∑ c, K₀ (.inr b) c * K₀ c y) = 0 := by
          ext a'
          rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hsq (.inr a') y]
          simp only [Finset.mul_sum, haug, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Fintype.sum_congr _ _ fun c => Fintype.sum_congr _ _ fun b => ?_
          rw [mul_assoc, hmid]
        exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hvec) a
  refine ⟨hcx₀, _root_.GlobalTheory.TorsExists.exists_torsSq O _ _root_.GlobalTheory.KeyKa.kdeg K₀ hcx₀ ?_⟩
  intro v hv
  have hz : ∀ x c, K₀ x (.inr c) = 0 := fun x c => kosD_inr_eq_zero m ev₀ x c
  have hmv : ∀ (u : _root_.GlobalTheory.KeyKa.KIx g d N → IsLocalRing.ResidueField O) y,
      (K₀.map (IsLocalRing.residue O)).mulVec u y = ∑ I : Finset (Fin g), ∑ l : Fin (N I.card),
        IsLocalRing.residue O (K₀ y (.inl ⟨I, l⟩)) * u (.inl ⟨I, l⟩) := by
    intro u y
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_sigma]
    simp [Matrix.map_apply, hz]
  have hmv₀ : ∀ (u : _root_.GlobalTheory.KeyKa.KIx g 0 N → IsLocalRing.ResidueField O) y,
      (_root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O))
        (fun _ => 0)).mulVec u y = ∑ I : Finset (Fin g), ∑ l : Fin (N I.card),
        _root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O))
          (fun _ => 0) y (.inl ⟨I, l⟩) * u (.inl ⟨I, l⟩) := by
    intro u y
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_sigma]
    simp
  have hent : ∀ (p q : (I : Finset (Fin g)) × Fin (N I.card)),
      IsLocalRing.residue O (K₀ (.inl p) (.inl q)) =
        _root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O))
          (fun _ => (0 : Matrix (Fin 0) _ _)) (.inl p) (.inl q) := fun p q =>
    map_kosD_inl_inl _ m ev₀ _ p q

  choose u0 hu0 using fun a : Fin d => IsLocalRing.residue_surjective (v (.inr a))
  obtain ⟨s, hs⟩ := hsurj u0

  choose sa hsa using fun a : Fin d => hsurj (Pi.single a 1)
  choose x hx using fun l : Fin (N 0) => IsLocalRing.residue_surjective (v (.inl ⟨∅, l⟩))
  have hc : ∀ a, IsLocalRing.residue O ((ev₀ 0).mulVec x a) = 0 := by
    intro a
    have h := congrFun hv (.inr a)
    rw [Pi.zero_apply, hmv, Finset.sum_eq_single (∅ : Finset (Fin g))] at h
    · rw [← h]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hx]
      rfl
    · intro I _ hI
      refine Finset.sum_eq_zero fun l _ => ?_
      show IsLocalRing.residue O (if I = ∅ then ev₀ I.card a l else 0) * _ = 0
      simp [hI]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  set s' : Fin (N 0) → O := ∑ a, (ev₀ 0).mulVec x a • sa a with hs'
  have hs'ev : (ev₀ 0).mulVec s' = (ev₀ 0).mulVec x := by
    ext a
    simp [hs', Matrix.mulVec_sum, Matrix.mulVec_smul, hsa, Finset.sum_apply, Pi.single_apply]
  have hs'res : ∀ l, IsLocalRing.residue O (s' l) = 0 := by
    intro l
    simp [hs', Finset.sum_apply, hc]
  have hx'0 : (ev 0).mulVec (x - s') = 0 := by
    rw [hev, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, hs'ev, sub_self, Matrix.mulVec_zero]
  obtain ⟨w1, hw1⟩ := hker (x - s') hx'0

  obtain ⟨w', hw'⟩ := hres (Sum.elim (fun p => v (.inl p)) (fun e => Fin.elim0 e)) (by
    ext z
    rcases z with ⟨I, l⟩ | e
    · have h := congrFun hv (.inl ⟨I, l⟩)
      rw [Pi.zero_apply, hmv] at h
      rw [hmv₀, Pi.zero_apply, ← h]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun l' _ => ?_
      rw [hent]
      rfl
    · exact Fin.elim0 e)
  let wf : (I : Finset (Fin g)) → Fin (N I.card) → IsLocalRing.ResidueField O := fun I l =>
    if hI : I = ∅ then IsLocalRing.residue O (s (Fin.cast (by simp [hI]) l))
    else if I.card = 1 then
      ∑ i, (if h : I = {i} then IsLocalRing.residue O (w1 i (Fin.cast (by simp [h]) l)) else 0)
    else w' (.inl ⟨I, l⟩)
  refine ⟨Sum.elim (fun p => wf p.1 p.2) (fun _ => 0), ?_⟩
  ext y
  rcases y with ⟨I, l⟩ | a
  · by_cases hI : I = ∅
    · subst hI
      obtain ⟨l, rfl⟩ : ∃ l' : Fin (N 0), l' = l := ⟨l, rfl⟩
      have hxl : IsLocalRing.residue O (x l) = ∑ i, ∑ l'' : Fin (N 1),
          IsLocalRing.residue O (m i 0 1 l l'') * IsLocalRing.residue O (w1 i l'') := by
        calc IsLocalRing.residue O (x l)
            = IsLocalRing.residue O ((∑ i, (m i 0 1).mulVec (w1 i)) l) := by
              rw [← hw1]
              show _ = IsLocalRing.residue O (x l - s' l)
              simp [hs'res]
          _ = _ := by simp [Finset.sum_apply, Matrix.mulVec, dotProduct, map_sum]
      refine Eq.trans ?_ (hx l)
      rw [hmv, hxl]
      have hJ : ∀ J : Finset (Fin g), ∑ l' : Fin (N J.card),
          IsLocalRing.residue O (K₀ (.inl ⟨∅, l⟩) (.inl ⟨J, l'⟩)) *
            Sum.elim (fun p : (I : Finset (Fin g)) × Fin (N I.card) => wf p.1 p.2)
              (fun _ : Fin d => (0 : IsLocalRing.ResidueField O)) (.inl ⟨J, l'⟩) =
          ∑ i, if J = {i} then ∑ l'' : Fin (N 1),
            IsLocalRing.residue O (m i 0 1 l l'') * IsLocalRing.residue O (w1 i l'') else 0 := by
        intro J
        by_cases h : ∃ i, J = {i}
        · obtain ⟨i, rfl⟩ := h
          rw [Finset.sum_eq_single i (fun j _ hj => if_neg fun h' => hj (Finset.singleton_inj.mp h').symm)
            (fun h' => absurd (Finset.mem_univ _) h'), if_pos rfl]
          refine Finset.sum_congr rfl fun l' _ => ?_
          congr 1
          · rw [hK₀]
            first
              | (simp [_root_.GlobalTheory.KeyKa.kosD]; done)
              | (simp [_root_.GlobalTheory.KeyKa.kosD]; rfl)
          · first
              | (simp [wf]; done)
              | (simp [wf]; rfl)
        · push_neg at h
          rw [Finset.sum_eq_zero fun i _ => if_neg (h i)]
          refine Finset.sum_eq_zero fun l' _ => ?_
          rw [hK₀]
          simp [_root_.GlobalTheory.KeyKa.kosD, h]
      rw [Finset.sum_congr rfl fun J _ => hJ J, Finset.sum_comm]
      simp
    · refine Eq.trans ?_ (hw' ⟨I, l⟩ hI).symm
      rw [hmv, hmv₀]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun l' _ => ?_
      by_cases hdeg : J.card = I.card + 1
      · have hJ0 : J ≠ ∅ := by
          rintro rfl
          simp at hdeg
        have hJ1 : J.card ≠ 1 := by
          intro h
          exact hI (Finset.card_eq_zero.mp (by omega))
        rw [hent]
        congr 1
        simp [wf, hJ0, hJ1]
      · have h0 : K₀ (.inl ⟨I, l⟩) (.inl ⟨J, l'⟩) = 0 :=
          hcx₀.1 _ _ (by show J.card + 1 ≠ I.card + 1 + 1; omega)
        rw [← hent, h0, map_zero, zero_mul, zero_mul]
  · rw [hmv, Finset.sum_eq_single (∅ : Finset (Fin g))]
    · rw [← hu0 a, ← hs]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      show IsLocalRing.residue O (if (∅ : Finset (Fin g)) = ∅ then ev₀ 0 a l else 0) * wf ∅ l = _
      first
        | (simp [wf]; done)
        | (simp [wf]; rfl)
        | rfl
        | (simp only [wf, ↓reduceDIte, ↓reduceIte]; rfl)
    · intro I _ hI
      refine Finset.sum_eq_zero fun l _ => ?_
      show IsLocalRing.residue O (if I = ∅ then ev₀ I.card a l else 0) * _ = 0
      simp [hI]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
end _root_.GlobalTheory.KeyKa.KoszulTors
end GlobalTheory.KeyKa.KoszulTors
