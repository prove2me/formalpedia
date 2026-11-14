-- Prove2me | solution 1 for Mazoit2013.bramble_from_flap_families
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T20:03:23.965374+00:00
-- url     : https://prove2.me/submissions/3c18d86c-20de-4e35-9250-d9e710dc58d4

import Definitions.Def_SeymourThomas1993_Brambles
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Push
set_option autoImplicit false
namespace StableMSR.Recovery.FlapFamilies
variable {V : Type} [DecidableEq V]

/-- A family of admissible flaps closed under enlargements that are still admissible. -/
def UpwardClosed (F B : Finset (Finset V)) : Prop :=
  B ⊆ F ∧ ∀ X ∈ B, ∀ Y ∈ F, X ⊆ Y → Y ∈ B

/-- The family contains a flap of every admissible partial decomposition. -/
def Hits (D : Finset (Finset (Finset V))) (B : Finset (Finset V)) : Prop :=
  ∀ d ∈ D, ∃ X ∈ d, X ∈ B

lemma exists_subset_minimal (B : Finset (Finset V)) {X : Finset V} (hX : X ∈ B) :
    ∃ Y ∈ B, Y ⊆ X ∧ ∀ Z ∈ B, Z ⊆ Y → Z = Y := by
  classical
  obtain ⟨Y,hY,hmin⟩ := Finset.exists_min_image (B.filter (fun Z => Z ⊆ X))
    Finset.card ⟨X,Finset.mem_filter.mpr ⟨hX,Finset.Subset.refl _⟩⟩
  obtain ⟨hYB,hYX⟩ := Finset.mem_filter.mp hY
  refine ⟨Y,hYB,hYX,?_⟩
  intro Z hZ hZY
  exact Finset.eq_of_subset_of_card_le hZY
    (hmin Z (Finset.mem_filter.mpr ⟨hZ,hZY.trans hYX⟩))

lemma erase_minimal_upward_closed {F B : Finset (Finset V)} (hB : UpwardClosed F B)
    {X : Finset V} (hmin : ∀ Y ∈ B, Y ⊆ X → Y = X) :
    UpwardClosed F (B.erase X) := by
  classical
  refine ⟨(Finset.erase_subset _ _).trans hB.1,?_⟩
  intro Y hY Z hZ hYZ
  obtain ⟨hne,hYB⟩ := Finset.mem_erase.mp hY
  apply Finset.mem_erase.mpr
  refine ⟨?_,hB.2 Y hYB Z hZ hYZ⟩
  intro he
  exact hne (hmin Y hYB (he ▸ hYZ))

lemma minimum_has_unique_witness {F B : Finset (Finset V)}
    {D : Finset (Finset (Finset V))} (hup : UpwardClosed F B) (hhit : Hits D B)
    (hminimum : ∀ C, UpwardClosed F C → Hits D C → B.card ≤ C.card)
    {X : Finset V} (hX : X ∈ B) (hmin : ∀ Y ∈ B, Y ⊆ X → Y = X) :
    ∃ d ∈ D, X ∈ d ∧ ∀ Y ∈ d, Y ∈ B → Y = X := by
  classical
  have hnot : ¬ Hits D (B.erase X) := by
    intro h
    exact Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hX)
      (hminimum (B.erase X) (erase_minimal_upward_closed hup hmin) h)
  unfold Hits at hnot
  push_neg at hnot
  obtain ⟨d,hd,havoid⟩ := hnot
  obtain ⟨Y,hYd,hYB⟩ := hhit d hd
  have he : Y = X := by
    by_contra hn
    exact havoid Y hYd (Finset.mem_erase.mpr ⟨hn,hYB⟩)
  refine ⟨d,hd,he ▸ hYd,?_⟩
  intro Z hZd hZB
  by_contra hn
  exact havoid Z hZd (Finset.mem_erase.mpr ⟨hn,hZB⟩)

/-- Mazoit's finite extremal argument. A gluing rule for non-touching flaps
forces a minimal upward-closed transversal of partial decompositions to touch
pairwise. The rule records only the new flaps' containment in old flaps. -/
theorem exists_touching_hitting_family
    (F : Finset (Finset V)) (D : Finset (Finset (Finset V)))
    (touch : Finset V → Finset V → Prop)
    (hfamilies : ∀ d ∈ D, d.Nonempty ∧ d ⊆ F)
    (hmono : ∀ X Y X' Y', X' ⊆ X → Y' ⊆ Y → touch X' Y' → touch X Y)
    (hglue : ∀ dX ∈ D, ∀ dY ∈ D, ∀ X ∈ dX, ∀ Y ∈ dY, ¬ touch X Y →
      ∃ d ∈ D, ∀ Z ∈ d,
        (∃ A ∈ dX, A ≠ X ∧ Z ⊆ A) ∨ (∃ A ∈ dY, A ≠ Y ∧ Z ⊆ A)) :
    ∃ B : Finset (Finset V), UpwardClosed F B ∧ Hits D B ∧
      ∀ X ∈ B, ∀ Y ∈ B, touch X Y := by
  classical
  have hupF : UpwardClosed F F := ⟨Finset.Subset.refl _,fun _ _ _ hY _ => hY⟩
  have hhitF : Hits D F := by
    intro d hd
    obtain ⟨X,hX⟩ := (hfamilies d hd).1
    exact ⟨X,hX,(hfamilies d hd).2 hX⟩
  have hex : ∃ n : ℕ, ∃ B : Finset (Finset V), UpwardClosed F B ∧ Hits D B ∧ B.card = n :=
    ⟨F.card,F,hupF,hhitF,rfl⟩
  obtain ⟨B,hup,hhit,hcard⟩ := Nat.find_spec hex
  have hminimum : ∀ C, UpwardClosed F C → Hits D C → B.card ≤ C.card := by
    intro C hC hCD
    rw [hcard]
    exact Nat.find_min' hex ⟨C,hC,hCD,rfl⟩
  refine ⟨B,hup,hhit,?_⟩
  intro X hX Y hY
  by_contra hn
  obtain ⟨X',hX'B,hX'sub,hX'min⟩ := exists_subset_minimal B hX
  obtain ⟨Y',hY'B,hY'sub,hY'min⟩ := exists_subset_minimal B hY
  have hnot : ¬ touch X' Y' := fun h => hn (hmono X Y X' Y' hX'sub hY'sub h)
  obtain ⟨dX,hdX,hX'd,hXuniq⟩ := minimum_has_unique_witness hup hhit hminimum hX'B hX'min
  obtain ⟨dY,hdY,hY'd,hYuniq⟩ := minimum_has_unique_witness hup hhit hminimum hY'B hY'min
  obtain ⟨d,hd,hnew⟩ := hglue dX hdX dY hdY X' hX'd Y' hY'd hnot
  obtain ⟨Z,hZd,hZB⟩ := hhit d hd
  rcases hnew Z hZd with ⟨A,hA,hne,hZA⟩ | ⟨A,hA,hne,hZA⟩
  · exact hne (hXuniq A hA (hup.2 Z hZB A ((hfamilies dX hdX).2 hA) hZA))
  · exact hne (hYuniq A hA (hup.2 Z hZB A ((hfamilies dY hdY).2 hA) hZA))

/-- If each small vertex set has a realizable family of connected flaps avoiding
it (the star decompositions), the extremal touching family has order at least k. -/
theorem exists_touching_unhittable_family
    (F : Finset (Finset V)) (D : Finset (Finset (Finset V)))
    (touch : Finset V → Finset V → Prop) (connected : Finset V → Prop) (k : ℕ)
    (hfamilies : ∀ d ∈ D, d.Nonempty ∧ d ⊆ F)
    (hmono : ∀ X Y X' Y', X' ⊆ X → Y' ⊆ Y → touch X' Y' → touch X Y)
    (hglue : ∀ dX ∈ D, ∀ dY ∈ D, ∀ X ∈ dX, ∀ Y ∈ dY, ¬ touch X Y →
      ∃ d ∈ D, ∀ Z ∈ d,
        (∃ A ∈ dX, A ≠ X ∧ Z ⊆ A) ∨ (∃ A ∈ dY, A ≠ Y ∧ Z ⊆ A))
    (hstar : ∀ W : Finset V, W.card < k →
      ∃ d ∈ D, ∀ X ∈ d, connected X ∧ Disjoint W X) :
    ∃ B : Finset (Finset V), B ⊆ F ∧ (∀ X ∈ B, connected X) ∧
      (∀ X ∈ B, ∀ Y ∈ B, touch X Y) ∧
      ∀ W : Finset V, W.card < k → ∃ X ∈ B, Disjoint W X := by
  classical
  obtain ⟨B,hup,hhit,htouch⟩ := exists_touching_hitting_family F D touch hfamilies hmono hglue
  refine ⟨B.filter connected,(Finset.filter_subset _ _).trans hup.1,?_,?_,?_⟩
  · intro X hX; exact (Finset.mem_filter.mp hX).2
  · intro X hX Y hY
    exact htouch X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1
  · intro W hW
    obtain ⟨d,hd,hflaps⟩ := hstar W hW
    obtain ⟨X,hXd,hXB⟩ := hhit d hd
    exact ⟨X,Finset.mem_filter.mpr ⟨hXB,(hflaps X hXd).1⟩,(hflaps X hXd).2⟩

end StableMSR.Recovery.FlapFamilies


namespace StableMSR.Recovery.Brambles
open Havens
lemma touch_mono {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {S T C D : Finset V}
    (hSC : S ⊆ C) (hTD : T ⊆ D) (ht : Touch G S T) : Touch G C D := by
  rcases ht with ⟨v,hvS,hvT⟩ | ⟨u,hu,v,hv,huv⟩
  · exact Or.inl ⟨v,hSC hvS,hTD hvT⟩
  · exact Or.inr ⟨u,hSC hu,v,hTD hv,huv⟩


/-- Mazoit's bramble extraction from realizable flap families. The hypotheses
are the nonemptiness, non-touching flap gluing, and star-decomposition properties.
No treewidth or bramble conclusion is assumed. -/
theorem bramble_from_flap_families {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (F : Finset (Finset V)) (D : Finset (Finset (Finset V))) (k : ℕ)
    (hfamilies : ∀ d ∈ D, d.Nonempty ∧ d ⊆ F)
    (hglue : ∀ dX ∈ D, ∀ dY ∈ D, ∀ X ∈ dX, ∀ Y ∈ dY, ¬ Touch G X Y →
      ∃ d ∈ D, ∀ Z ∈ d,
        (∃ A ∈ dX, A ≠ X ∧ Z ⊆ A) ∨ (∃ A ∈ dY, A ≠ Y ∧ Z ⊆ A))
    (hstar : ∀ W : Finset V, W.card < k →
      ∃ d ∈ D, ∀ X ∈ d, ConnectedSet G X ∧ Disjoint W X) :
    ∃ B : Finset (Finset V), B ⊆ F ∧ IsBramble G B ∧ OrderAtLeast B k := by
  obtain ⟨B,hBF,hconnected,htouch,horder⟩ :=
    FlapFamilies.exists_touching_unhittable_family F D (Touch G) (ConnectedSet G) k
      hfamilies (fun _ _ _ _ hX hY h => touch_mono hX hY h) hglue hstar
  exact ⟨B,hBF,⟨hconnected,htouch⟩,horder⟩


end StableMSR.Recovery.Brambles

open StableMSR.Recovery.Brambles StableMSR.Recovery.Havens
theorem solution {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (F : Finset (Finset V)) (D : Finset (Finset (Finset V))) (k : ℕ)
    (hfamilies : ∀ d ∈ D, d.Nonempty ∧ d ⊆ F)
    (hglue : ∀ dX ∈ D, ∀ dY ∈ D, ∀ X ∈ dX, ∀ Y ∈ dY, ¬ Touch G X Y →
      ∃ d ∈ D, ∀ Z ∈ d,
        (∃ A ∈ dX, A ≠ X ∧ Z ⊆ A) ∨ (∃ A ∈ dY, A ≠ Y ∧ Z ⊆ A))
    (hstar : ∀ W : Finset V, W.card < k →
      ∃ d ∈ D, ∀ X ∈ d, ConnectedSet G X ∧ Disjoint W X) :
    ∃ B : Finset (Finset V), B ⊆ F ∧ IsBramble G B ∧ OrderAtLeast B k := by
  exact bramble_from_flap_families G F D k hfamilies hglue hstar
