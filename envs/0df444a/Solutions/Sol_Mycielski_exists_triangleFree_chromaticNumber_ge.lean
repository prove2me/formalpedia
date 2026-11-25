-- Prove2me | solution 1 for Mycielski.exists_triangleFree_chromaticNumber_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:36:24.034466+00:00
-- url     : https://prove2.me/submissions/d3822250-c157-4b82-b932-f2b0efbc301b

module
public import Definitions.Def_Mycielski_Coloring
public import Definitions.Def_Mycielski_Family
public import Theorems.Thm_Mycielski_family_cliqueFree_three
public import Theorems.Thm_Mycielski_family_chromaticNumber

set_option autoImplicit true
@[expose] public section
public section
open Mycielski
open SimpleGraph
namespace Mycielski
theorem _root_.solution (k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 3 ∧ (k : ℕ∞) ≤ G.chromaticNumber := by
  classical
  let e := Fintype.equivFin (FamilyVertex k)
  let G := (family k).map e.toEmbedding
  refine ⟨_, G, ?_, ?_⟩
  · exact (cliqueFree_map_iff).mpr (family_cliqueFree_three k)
  · have hmono := chromaticNumber_mono_of_hom (Hom.map e (family k)
      (fun {u v} h heq => (family k).ne_of_adj h (e.injective heq)))
    have hk : (k : ℕ∞) ≤ (family k).chromaticNumber := by
      rw [family_chromaticNumber]
      exact_mod_cast (Nat.le_add_right k 2)
    exact hk.trans hmono
end Mycielski
