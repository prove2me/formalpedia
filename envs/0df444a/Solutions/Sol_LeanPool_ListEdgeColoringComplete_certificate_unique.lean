-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.certificate_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:27:38.310813+00:00
-- url     : https://prove2.me/submissions/02aa5a6a-436a-464c-9be9-98dc4b45662a

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_isLowEnd_iff_not
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_edgeKey_comm
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_edgeKey_lt_of_precedes
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_localRank_add
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_localRank_ne_blockedRank
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_localRank_injective
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_forcing
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_canonicalRow_injective

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
variable {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution (r : Fin n → Fin n → Fin n)
    (hinj : ∀ i, Function.Injective (r i))
    (hdiag : ∀ i, (r i i : ℕ) = blockedRank n i)
    (hsum : ∀ i j, i ≠ j → (r i j : ℕ) + r j i = targetDegree n i j) :
    r = canonicalRow := by
  -- claim for an unordered edge
  let C : Fin n → Fin n → Prop := fun u v =>
    (r u v : ℕ) = localRank n u v ∧ (r v u : ℕ) = localRank n v u
  have hsurj : ∀ i, Function.Surjective (r i) := fun i =>
    Finite.injective_iff_surjective.mp (hinj i)
  have hcanSurj : ∀ i, Function.Surjective (canonicalRow (n := n) i) := fun i =>
    Finite.injective_iff_surjective.mp (canonicalRow_injective i)
  have key : ∀ k, ∀ u v : Fin n, u ≠ v → edgeKey n u v = k → C u v := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IH =>
    intro u v huv hk
    have IH' : ∀ u' v' : Fin n, u' ≠ v' → ∀ a b : Fin n, a ≠ b →
        edgeKey n a b = k → Precedes n u' v' a b → C u' v' := by
      intro u' v' huv' a b _ hab hp
      exact IH _ (hab ▸ edgeKey_lt_of_precedes u'.isLt v'.isLt a.isLt b.isLt hp) u' v'
        huv' rfl
    -- the main step, for an orientation `(a, b)` with low end `b`
    have step : ∀ a b : Fin n, a ≠ b → edgeKey n a b = k → ¬ IsLowEnd n a b →
        (r a b : ℕ) = localRank n a b := by
      intro a b hab hk' hlow
      have habv : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
      obtain ⟨l, hl⟩ := hsurj a ⟨localRank n a b, localRank_lt a.isLt b.isLt⟩
      have hl' : (r a l : ℕ) = localRank n a b := congrArg Fin.val hl
      by_cases hlb : l = b
      · subst hlb; exact hl'
      exfalso
      have hlbv : (l : ℕ) ≠ b := fun h => hlb (Fin.ext h)
      have hla : l ≠ a := by
        intro h
        rw [h] at hl'
        exact localRank_ne_blockedRank a.isLt b.isLt habv (hl' ▸ hdiag a)
      have halv : (a : ℕ) ≠ l := fun h => hla (Fin.ext h).symm
      by_cases hp : Precedes n a l a b
      · have := (IH' a l (Ne.symm hla) a b hab hk' hp).1
        exact hlbv (localRank_injective a.isLt l.isLt b.isLt halv habv (this ▸ hl'))
      · have hs := hsum a l (Ne.symm hla)
        obtain ⟨x, hx⟩ := hcanSurj l (r l a)
        have hxv : (canonicalRow l x : ℕ) = r l a := congrArg Fin.val hx
        have hxl : x ≠ l := by
          intro h
          rw [h] at hxv
          have : r l l = r l a := by
            apply Fin.ext; rw [hdiag, ← hxv]; simp [canonicalRow, fullRank]
          exact hla (hinj l this)
        have hxlv : (x : ℕ) ≠ l := fun h => hxl (Fin.ext h)
        have hxr : localRank n l x = r l a := by
          rw [← hxv]; simp [canonicalRow, fullRank, Ne.symm hxlv]
        have hxa : x ≠ a := by
          intro h
          rw [h] at hxr
          have h1 := localRank_add a.isLt l.isLt halv
          have : localRank n a l = localRank n a b := by omega
          exact hlbv (localRank_injective a.isLt l.isLt b.isLt halv habv this)
        have hxav : (x : ℕ) ≠ a := fun h => hxa (Fin.ext h)
        have hf := forcing a.isLt b.isLt l.isLt x.isLt hlow hlbv hxlv hxav hp (by omega)
        have := (IH' l x (Ne.symm hxl) a b hab hk' hf).1
        exact hxa (hinj l (Fin.ext (by rw [this, hxr])))
    have huvv : (u : ℕ) ≠ v := fun h => huv (Fin.ext h)
    have hkey := edgeKey_comm n u v
    by_cases hlow : IsLowEnd n u v
    · have hvu := (isLowEnd_iff_not v.isLt huvv).mp hlow
      have h2 := step v u (Ne.symm huv) (hkey ▸ hk) hvu
      have hs := hsum u v huv
      have ha := localRank_add u.isLt v.isLt huvv
      exact ⟨by omega, h2⟩
    · have h1 := step u v huv hk hlow
      have hs := hsum u v huv
      have ha := localRank_add u.isLt v.isLt huvv
      exact ⟨h1, by omega⟩
  funext i j
  apply Fin.ext
  by_cases hij : i = j
  · subst hij
    rw [hdiag]
    simp [canonicalRow, fullRank]
  · have hijv : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rw [(key _ i j hij rfl).1]
    simp [canonicalRow, fullRank, hijv]
end LeanPool.ListEdgeColoringComplete
