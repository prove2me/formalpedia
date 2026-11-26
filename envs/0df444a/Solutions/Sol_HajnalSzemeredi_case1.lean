-- Prove2me | solution 1 for HajnalSzemeredi.case1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:52.152916+00:00
-- url     : https://prove2.me/submissions/1d7e5694-cd24-466b-9b74-a4b2e98971fb

module
public import Definitions.Def_HajnalSzemeredi_Shift
public import Definitions.Def_HajnalSzemeredi_Structure
public import Definitions.Def_HajnalSzemeredi_Cases
public import Theorems.Thm_HajnalSzemeredi_isEq_combine
public import Theorems.Thm_HajnalSzemeredi_Ctx_T_subset
public import Theorems.Thm_HajnalSzemeredi_Ctx_acc_subset
public import Theorems.Thm_HajnalSzemeredi_Ctx_lo_mem_acc
public import Theorems.Thm_HajnalSzemeredi_Ctx_lo_notMem_T
public import Theorems.Thm_HajnalSzemeredi_Ctx_mem_acc_of_mov
public import Theorems.Thm_HajnalSzemeredi_cls_update_old
public import Theorems.Thm_HajnalSzemeredi_cls_update_other
public import Theorems.Thm_HajnalSzemeredi_cls_update_self
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
public import Theorems.Thm_HajnalSzemeredi_proper_update
public import Theorems.Thm_HajnalSzemeredi_shift_of_acc
public import Theorems.Thm_HajnalSzemeredi_transfer
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr


section
@[expose] public section
noncomputable section
open Classical Finset Relation
namespace HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
private lemma proper_mono' {S T : Finset V} {f : V → ℕ} (h : Proper G S f) (hT : T ⊆ S) :
    Proper G T f :=
  fun v hv w hw => h v (hT hv) w (hT hw)
private lemma proper_insert_update {T : Finset V} {f : V → ℕ} {v : V} {j : ℕ}
    (h : Proper G T f) (hmov : Movable G T f v j) :
    Proper G (insert v T) (Function.update f v j) := by
  intro a ha b hb hab
  by_cases hav : a = v
  · subst hav
    have hba : b ≠ a := fun h => G.loopless.irrefl _ (h ▸ hab)
    have hbT : b ∈ T := (mem_insert.mp hb).resolve_left hba
    simp only [Function.update_self, Function.update_of_ne hba]
    intro hjb
    exact hmov b (mem_cls.mpr ⟨hbT, hjb.symm⟩) hab
  · have haT : a ∈ T := (mem_insert.mp ha).resolve_left hav
    by_cases hbv : b = v
    · subst hbv
      simp only [Function.update_self, Function.update_of_ne hav]
      intro hja
      exact hmov a (mem_cls.mpr ⟨haT, hja⟩) hab.symm
    · have hbT : b ∈ T := (mem_insert.mp hb).resolve_left hbv
      simpa [Function.update_of_ne hav, Function.update_of_ne hbv] using h a haT b hbT hab
private lemma cls_insert_update_self {T : Finset V} {f : V → ℕ} {v : V} {j : ℕ} :
    cls (insert v T) (Function.update f v j) j = insert v (cls T f j) := by
  ext w
  by_cases hw : w = v
  · subst hw; simp
  · simp [hw]
private lemma cls_insert_update_ne {T : Finset V} {f : V → ℕ} {v : V} {i j : ℕ}
    (hv : v ∉ T) (hij : i ≠ j) :
    cls (insert v T) (Function.update f v j) i = cls T f i := by
  ext w
  by_cases hw : w = v
  · subst hw; simp [hv, Ne.symm hij]
  · simp [hw]
private lemma cls_part {S : Finset V} {c : V → ℕ} {Q : Finset ℕ} {i : ℕ} (hi : i ∈ Q) :
    cls (part S c Q) c i = cls S c i := by
  ext w
  simp only [mem_cls, part, mem_filter]
  constructor
  · rintro ⟨⟨hw, -⟩, hc⟩; exact ⟨hw, hc⟩
  · rintro ⟨hw, hc⟩; exact ⟨⟨hw, hc ▸ hi⟩, hc⟩
private lemma solo_eq {S : Finset V} {c : V → ℕ} {y z u : V} {W : ℕ}
    (h : nIn G S c y W = {z}) (hu : u ∈ S) (hcu : c u = W) (hadj : G.Adj y u) : u = z := by
  have : u ∈ nIn G S c y W := mem_inter.mpr ⟨mem_nbr.mpr ⟨hu, hadj⟩, mem_cls.mpr ⟨hu, hcu⟩⟩
  rw [h] at this
  exact mem_singleton.mp this
private lemma reach_restrict {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {r s lo hi : ℕ}
    (h : Ctx G S P c r s lo hi) {R : ℕ → ℕ → Prop}
    (hR : ∀ a b, R a b → Mov G S c a b) {X : ℕ} (hX : ReflTransGen R X lo) :
    ReflTransGen (fun a b => R a b ∧ a ∈ acc G S P c lo ∧ b ∈ acc G S P c lo) X lo := by
  have key : ∀ a, ReflTransGen R a lo → a ∈ acc G S P c lo ∧
      ReflTransGen (fun a b => R a b ∧ a ∈ acc G S P c lo ∧ b ∈ acc G S P c lo) a lo := by
    intro a ha
    induction ha using ReflTransGen.head_induction_on with
    | refl => exact ⟨h.lo_mem_acc, ReflTransGen.refl⟩
    | head hab _ ih =>
      have hm := h.mem_acc_of_mov (hR _ _ hab) ih.1
      exact ⟨hm, ReflTransGen.head ⟨hab, hm, ih.1⟩ ih.2⟩
  exact (key X hX).2
end HajnalSzemeredi
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
namespace HajnalSzemeredi
theorem _root_.solution {S : Finset V} {P : Finset ℕ} {c g : V → ℕ} {r s lo hi U : ℕ} {z y₁ : V}
    (h : Ctx G S P c r s lo hi)
    (hterm : ∀ W ∈ T G S P c lo U, ∀ X ∈ (acc G S P c lo).erase W,
      ReflTransGen (avoid G S c W) X lo)
    (hzS : z ∈ S) (hzT : c z ∈ T G S P c lo U)
    (hy₁ : y₁ ∈ Sz G S c (T G S P c lo U) (part S c (P \ acc G S P c lo)) z)
    (hX : ∃ X ∈ acc G S P c lo, X ≠ c z ∧ Movable G S c z X)
    (hg : IsEq G ((part S c (P \ acc G S P c lo)).erase y₁) (P \ acc G S P c lo) g s) :
    ∃ c', IsEq G S P c' s := by
  obtain ⟨X, hXacc, hXW, hXmov⟩ := hX
  set PA := acc G S P c lo with hPA
  set PB := P \ PA with hPB
  set A := part S c PA with hA
  set B := part S c PB with hB
  have hWacc : c z ∈ PA := (mem_erase.mp (Ctx.T_subset U hzT)).2
  have hWlo : c z ≠ lo := by
    intro e
    have hz' := hzT
    rw [e] at hz'
    exact Ctx.lo_notMem_T U hz'
  have hWhi : c z ≠ hi := fun e => h.hi_not (e ▸ hWacc)
  have hWcard : (cls S c (c z)).card = s := h.near.card _ (Ctx.acc_subset hWacc) hWlo hWhi
  obtain ⟨hy₁B, hsolo⟩ := mem_filter.mp hy₁
  obtain ⟨-, -, -, hsolo₁⟩ := hsolo
  have hy₁S : y₁ ∈ S := (mem_filter.mp hy₁B).1
  have hy₁PB : c y₁ ∈ PB := (mem_filter.mp hy₁B).2
  have hy₁PA : c y₁ ∉ PA := (mem_sdiff.mp hy₁PB).2
  have hzA : z ∈ A := mem_filter.mpr ⟨hzS, hWacc⟩
  have hy₁A : y₁ ∉ A := fun hh => hy₁PA (mem_filter.mp hh).2
  have hXlo_hi : X ≠ hi := fun e => h.hi_not (e ▸ hXacc)
  set c1 := Function.update c z X with hc1
  set φ := Function.update c1 y₁ (c z) with hφ
  set SA := insert y₁ A with hSA
  have hc1prop : Proper G A c1 :=
    proper_mono' (proper_update h.near.proper hXmov) (filter_subset _ _)
  have hmov1 : Movable G A c1 y₁ (c z) := by
    intro w hw hadj
    rw [mem_cls] at hw
    have hwz : w ≠ z := by
      rintro rfl
      rw [hc1, Function.update_self] at hw
      exact hXW hw.2
    rw [hc1, Function.update_of_ne hwz] at hw
    exact hwz (solo_eq hsolo₁ (mem_filter.mp hw.1).1 hw.2 hadj)
  have hprop : Proper G SA φ := proper_insert_update hc1prop hmov1
  have hinto : Into SA φ PA := by
    intro v hv
    by_cases hvy : v = y₁
    · subst hvy; simpa [hφ] using hWacc
    · have hvA : v ∈ A := (mem_insert.mp hv).resolve_left hvy
      rw [hφ, Function.update_of_ne hvy]
      by_cases hvz : v = z
      · subst hvz; simpa [hc1] using hXacc
      · rw [hc1, Function.update_of_ne hvz]; exact (mem_filter.mp hvA).2
  have hclsW : cls SA φ (c z) = insert y₁ ((cls S c (c z)).erase z) := by
    rw [hSA, hφ, cls_insert_update_self, hc1, cls_update_old hzA hXW.symm, cls_part hWacc]
  have hclsWcard : (cls SA φ (c z)).card = s := by
    rw [hclsW, card_insert_of_notMem, card_erase_of_mem (mem_cls.mpr ⟨hzS, rfl⟩), hWcard]
    · have : 0 < s := hWcard ▸ card_pos.mpr ⟨z, mem_cls.mpr ⟨hzS, rfl⟩⟩
      omega
    · intro hm
      exact hy₁PA ((mem_cls.mp (mem_erase.mp hm).2).2 ▸ hWacc)
  have hclsX : cls SA φ X = insert z (cls S c X) := by
    rw [hSA, hφ, cls_insert_update_ne hy₁A hXW, hc1, cls_update_self hzA, cls_part hXacc]
  have hclsXcard : (cls SA φ X).card = (cls S c X).card + 1 := by
    rw [hclsX, card_insert_of_notMem]
    intro hm
    exact hXW (mem_cls.mp hm).2.symm
  have hclsO : ∀ i ∈ PA, i ≠ c z → i ≠ X → cls SA φ i = cls S c i := by
    intro i hi hiW hiX
    rw [hSA, hφ, cls_insert_update_ne hy₁A hiW, hc1, cls_update_other hiX hiW, cls_part hi]
  have hEqA : ∃ cA, IsEq G SA PA cA s := by
    by_cases hXlo : X = lo
    · refine ⟨φ, hprop, hinto, fun i hi' => ?_⟩
      by_cases hiW : i = c z
      · rw [hiW]; exact hclsWcard
      by_cases hiX : i = X
      · rw [hiX, hclsXcard, hXlo]; exact h.near.card_lo
      rw [hclsO i hi' hiW hiX]
      exact h.near.card i (Ctx.acc_subset hi') (hXlo ▸ hiX) (fun e => h.hi_not (e ▸ hi'))
    · have hXcard : (cls S c X).card = s := h.near.card X (Ctx.acc_subset hXacc) hXlo hXlo_hi
      have hnear : IsNear G SA PA φ s lo X := by
        refine ⟨hprop, hinto, h.lo_mem_acc, hXacc, Ne.symm hXlo, ?_, ?_, ?_⟩
        · rw [hclsO lo h.lo_mem_acc (Ne.symm hWlo) (Ne.symm hXlo)]; exact h.near.card_lo
        · rw [hclsXcard, hXcard]
        · intro i hi' hilo hiX
          by_cases hiW : i = c z
          · rw [hiW]; exact hclsWcard
          rw [hclsO i hi' hiW hiX]
          exact h.near.card i (Ctx.acc_subset hi') hilo (fun e => h.hi_not (e ▸ hi'))
      refine shift_of_acc hnear ?_
      have hp := reach_restrict h (fun a b hab => hab.1)
        (hterm (c z) hzT X (mem_erase.mpr ⟨hXW, hXacc⟩))
      refine transfer hp fun a b hab hbX => ?_
      obtain ⟨⟨⟨v, hv, hvmov⟩, haW, hbW⟩, haA, hbA⟩ := hab
      rw [mem_cls] at hv
      have hvz : v ≠ z := by rintro rfl; exact haW hv.2.symm
      have hvy : v ≠ y₁ := by rintro rfl; exact hy₁PA (hv.2 ▸ haA)
      refine ⟨v, mem_cls.mpr ⟨mem_insert_of_mem (mem_filter.mpr ⟨hv.1, hv.2 ▸ haA⟩), ?_⟩, ?_⟩
      · rw [hφ, Function.update_of_ne hvy, hc1, Function.update_of_ne hvz]; exact hv.2
      · intro u hu
        rw [hclsO b hbA hbW hbX] at hu
        exact hvmov u hu
  obtain ⟨cA, hcA⟩ := hEqA
  refine ⟨_, isEq_combine hcA hg ?_ ?_ (union_sdiff_of_subset Ctx.acc_subset) disjoint_sdiff⟩
  · ext v
    constructor
    · intro hv
      rcases mem_union.mp hv with hv | hv
      · rcases mem_insert.mp hv with rfl | hv
        · exact hy₁S
        · exact (mem_filter.mp hv).1
      · exact (mem_filter.mp (mem_erase.mp hv).2).1
    · intro hv
      by_cases hvy : v = y₁
      · subst hvy; exact mem_union_left _ (mem_insert_self _ _)
      by_cases hvA : c v ∈ PA
      · exact mem_union_left _ (mem_insert_of_mem (mem_filter.mpr ⟨hv, hvA⟩))
      · exact mem_union_right _
          (mem_erase.mpr ⟨hvy, mem_filter.mpr ⟨hv, mem_sdiff.mpr ⟨h.near.into v hv, hvA⟩⟩⟩)
  · rw [disjoint_left]
    intro v hv1 hv2
    obtain ⟨hvy, hvB⟩ := mem_erase.mp hv2
    rcases mem_insert.mp hv1 with rfl | hvA
    · exact hvy rfl
    · exact (mem_sdiff.mp (mem_filter.mp hvB).2).2 (mem_filter.mp hvA).2
end HajnalSzemeredi
