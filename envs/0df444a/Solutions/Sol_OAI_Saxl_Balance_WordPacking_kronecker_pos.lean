-- Prove2me | solution 1 for OAI.Saxl.Balance.WordPacking.kronecker_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:11:06.194456+00:00
-- url     : https://prove2.me/submissions/11f33c1b-d649-4ad6-b88c-e636230505f2

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Theorems.Thm_OAI_Saxl_Balance_balance_support_of_surjective
import Theorems.Thm_OAI_Saxl_young_orbit_map_uts

section
-- module Solutions.OAIQ259_US.Saxl_Basic
attribute [-instance] _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/
theorem intertwining_finrank_pos_iff {G : Type uG} {V : Type uV} {W : Type uW} [Group G]
    [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    0 < Module.finrank ℂ (Representation.IntertwiningMap ρ σ) ↔
      ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 :=
  Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := Representation.IntertwiningMap ρ σ)

theorem kronecker_pos_iff {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) :
    0 < kronecker a b t ↔
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        ((spechtRep a).tprod (spechtRep b)), f ≠ 0 := by
  exact @intertwining_finrank_pos_iff (Equiv.Perm (Fin n)) (Specht t)
    (Specht a ⊗[ℂ] Specht b) _ _ _ _ _ _ _
    (spechtRep t) ((spechtRep a).tprod (spechtRep b))

/- Column permutations cannot also fix the row word unless they are identity. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OneExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One Extra. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma intertwining_comp_ne_zero {G X Y Z : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap σ τ) (hF : Function.Injective F)
    (f : Representation.IntertwiningMap ρ σ) (hf : f ≠ 0) : F.comp f ≠ 0 := by
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have hh := congrArg (fun H => H x) hz
  exact hh.trans (map_zero F).symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SupportTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support Transport. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

namespace SupportLE
variable {G H X Y Z : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    [AddCommMonoid Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}

lemma detects_map {W : Type*} [AddCommMonoid W] [Module ℂ W]
    {υ : Representation ℂ G W} (h : SupportLE ρ σ)
    (f : Representation.IntertwiningMap υ ρ) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap υ σ, g ≠ 0 := by
  have hn : ∃ x, f x ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hf (Representation.IntertwiningMap.ext (LinearMap.ext hh))
  obtain ⟨x,hx⟩ := hn
  obtain ⟨g,hg⟩ := h (f x) hx
  exact ⟨g.comp f,fun hz => hg (congrArg (fun F : Representation.IntertwiningMap υ σ => F x) hz)⟩

end SupportLE

end Saxl

namespace Saxl

lemma coindEval_ne_zero {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap ρ (Representation.coind φ σ)) (hf : f ≠ 0) :
    coindEval φ f ≠ 0 := by
  intro hz
  apply hf
  rw [← coindLift_eval φ f,hz]
  ext x g
  rfl

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_PackingSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packing Support. -/

section

noncomputable section
open scoped TensorProduct MonoidAlgebra
namespace Saxl

theorem young_cyclic_support {n : ℕ} (θ μ : YoungDiagram) (t : Tableau n μ)
    (hc : μ.card = θ.card) (hd : Dominates μ θ)
    (w : Fin n → Fin (θ.colLen 0)) (f : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = f j)).card = θ.rowLen j) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n (θ.colLen 0)) (Pi.single w 1)).toRepresentation, F ≠ 0 := by
  obtain ⟨F,hF⟩ := young_orbit_map_uts θ μ t hc hd w f hw
  let Q := F.comp (subrepInclusion (cyclic (wordRep n (θ.colLen 0)) (Pi.single w 1)))
  have hQ : Q ≠ 0 := by
    intro h0
    exact hF (congrArg (fun T : Representation.IntertwiningMap
      (cyclic (wordRep n (θ.colLen 0)) (Pi.single w 1)).toRepresentation (spechtRep t) =>
        T ⟨Pi.single w 1,mem_cyclic _ _⟩) h0)
  exact intertwining_reverse_nonzero Q hQ

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Induction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

theorem kronecker_pos_of_packing {n : ℕ} {G Y : Type*}
    [Group G] [Finite G] [AddCommGroup Y] [Module ℂ Y]
    {lam μ : YoungDiagram} (a : Tableau n lam) (t : Tableau n μ)
    (c : Fin n → ℕ)
    (A : Fin (lam.colLen 0 * lam.colLen 0) → Prop)
    (label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → output a < output b)
    (φ : G →* fiberGroup c) (hφ : Function.Surjective φ)
    (τ : Representation ℂ G Y)
    (L : Y →ₗ[ℂ] WordSpace n (lam.colLen 0 * lam.colLen 0))
    (hm : ∀ y, L y ∈ (spechtTensorMap a a).range)
    (hs : ∀ y, FixedComponentSums c (fun a => (output a : ℤ)) σ (L y))
    (T : Representation.IntertwiningMap τ
      ((wordRep n (lam.colLen 0 * lam.colLen 0)).comp ((fiberGroup c).subtype.comp φ)))
    (hT : Function.Injective T)
    (he : ∀ y, coordinateProjection (componentWords c A label) (L y) = T y)
    (θ : YoungDiagram) (hc : μ.card = θ.card) (hd : Dominates μ θ)
    (w : Fin n → Fin (θ.colLen 0)) (e : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = e j)).card = θ.rowLen j)
    (hpack : SupportLE (cyclic (wordRep n (θ.colLen 0)) (Pi.single w 1)).toRepresentation
      (Representation.coind ((fiberGroup c).subtype.comp φ) τ)) :
    0 < kronecker a a t := by
  obtain ⟨F,hF⟩ := young_cyclic_support θ μ t hc hd w e hw
  obtain ⟨Q,hQ⟩ := hpack.detects_map F hF
  obtain ⟨R,hR⟩ := balance_support_of_surjective (spechtRep t)
    (spechtTensorMap a a).range c A label (fun a => (output a : ℤ)) σ
    (fun a b ha hb hab => by exact_mod_cast ho a b ha hb hab)
    φ hφ τ L hm hs T hT he
    (coindEval ((fiberGroup c).subtype.comp φ) Q)
    (coindEval_ne_zero ((fiberGroup c).subtype.comp φ) Q hQ)
  let : AddCommGroup (Specht a ⊗[ℂ] Specht a) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨i,hi⟩ := subrepresentation_embeds_of_le_range (spechtTensorMap a a)
    (spechtTensorMap a a).range le_rfl
  exact (kronecker_pos_iff a a t).mpr
    ⟨i.comp R,intertwining_comp_ne_zero i hi R hR⟩

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Gluing. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

theorem Piece.kronecker_pos {n : ℕ} {G Y : Type*}
    [Group G] [Finite G] [AddCommGroup Y] [Module ℂ Y]
    {lam μ : YoungDiagram} (a : Tableau n lam) (t : Tableau n μ)
    {c : Fin n → ℕ} {A : Fin (lam.colLen 0 * lam.colLen 0) → Prop}
    {label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ} {σ : ℕ → ℤ}
    {φ : G →* fiberGroup c} {τ : Representation ℂ G Y}
    (P : Piece (polytabloid a) c A label σ φ τ)
    (ho : ∀ a b, A a → A b → label a < label b → output a < output b)
    (θ : YoungDiagram) (hc : μ.card = θ.card) (hd : Dominates μ θ)
    (w : Fin n → Fin (θ.colLen 0)) (e : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = e j)).card = θ.rowLen j)
    (hpack : SupportLE (cyclic (wordRep n (θ.colLen 0)) (Pi.single w 1)).toRepresentation
      (Representation.coind ((fiberGroup c).subtype.comp φ) τ)) :
    0 < kronecker a a t := by
  exact kronecker_pos_of_packing a t c A label σ ho φ P.surj τ P.raw (by
    intro y
    obtain ⟨z,hz⟩ := P.raw_mem y
    exact ⟨z, by rw [←cyclicSquareMap_polytabloid]; exact hz⟩)
    P.raw_sums P.projected P.injective P.projection_eq θ hc hd w e hw hpack

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalancePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Packing. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

theorem Packing.kronecker_pos {n : ℕ} {lam μ θ : YoungDiagram}
    (a : Tableau n lam) (t : Tableau n μ)
    {A : Fin (lam.colLen 0 * lam.colLen 0) → Prop}
    {label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ}
    (w : Fin n → Fin (θ.colLen 0))
    (P : Packing (polytabloid a) A label (Pi.single w 1))
    (ho : ∀ x y, A x → A y → label x < label y → output x < output y)
    (hc : μ.card = θ.card) (hd : Dominates μ θ)
    (e : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = e j)).card = θ.rowLen j) :
    0 < kronecker a a t :=
  P.piece.kronecker_pos a t ho θ hc hd w e hw P.support

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

lemma sum_wordContent {n d : ℕ} (w : Fin n → Fin d) :
    ∑ j, wordContent w j = n := by
  classical
  simp only [wordContent,Finset.card_filter]
  rw [Finset.sum_comm]
  simp

namespace Balance
open FlagColumns Columns

lemma WordPacking.total {rs ps : List ℕ} {d : ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {marks : Finset ℕ}
    (P : WordPacking rs ps d A label marks) : ps.sum = rs.sum := by
  calc
    ps.sum = ∑ j, ps.get j := by rw [← List.sum_ofFn, List.ofFn_get]
    _ = ∑ j, wordContent P.word j := Finset.sum_congr rfl (fun j _ => (P.counts j).symm)
    _ = rs.sum := sum_wordContent P.word

theorem WordPacking.kronecker_pos_oai {rs ps : List ℕ} {lam μ : YoungDiagram}
    (a : Tableau rs.sum lam) (t : Tableau rs.sum μ)
    {A : Fin (lam.colLen 0 * lam.colLen 0) → Prop}
    {label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ} {marks : Finset ℕ}
    (P : WordPacking rs ps (lam.colLen 0) A label marks)
    (hv : blocks rs (standard (lam.colLen 0)) = polytabloid a)
    (hp : ∀ p ∈ ps, 0 < p)
    (ho : ∀ x y, A x → A y → label x < label y → output x < output y)
    (hd : Dominates μ (columnShape ps).transpose) : 0 < kronecker a a t := by
  let θ := (columnShape ps).transpose
  let Q := P.sorted hp
  let q : Fin θ.rowLens.length ≃ Fin (θ.colLen 0) := finCongr YoungDiagram.length_rowLens
  let w := q ∘ Q.word
  let R := (Q.packing.map (letterLift q)).congr hv (letterLift_single q Q.word)
  apply R.kronecker_pos a t w ho _ hd (Equiv.refl _) _
  · have hc : μ.card = rs.sum := by
      simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr t).symm
    rw [hc, show θ.card = ps.sum from by simp only [θ,transpose_card,columnShape_card]]
    exact P.total.symm
  · intro j
    change wordContent w j = θ.rowLen j
    rw [wordContent_lift_equiv,Q.counts]
    exact YoungDiagram.get_rowLens

end Balance
end Saxl
end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.Balance.WordPacking.kronecker_pos_oai := @OAI.Saxl.Balance.WordPacking.kronecker_pos_oai
