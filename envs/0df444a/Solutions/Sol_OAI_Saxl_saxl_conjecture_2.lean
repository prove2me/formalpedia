-- Prove2me | solution 2 for OAI.Saxl.saxl_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:35:25.583702+00:00
-- url     : https://prove2.me/submissions/1df26270-e43f-4d48-b53f-5335ec312903

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/Main.lean:L88-L88
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Saxl.saxl_conjecture.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Saxl_saxl_conjecture) verbatim and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseSign
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedQuotient
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripReduction
import Theorems.Thm_OAI_Saxl_dominated_support
import Theorems.Thm_OAI_Saxl_polytabloid_rowWord
import Theorems.Thm_OAI_Saxl_shiftedStairWord_support
import Theorems.Thm_OAI_Saxl_staircase_cut_layers
import Theorems.Thm_OAI_Saxl_staircase_projected_ne_zero
import Theorems.Thm_OAI_Saxl_strip_product_support
import Theorems.Thm_OAI_Saxl_strip_reduction
import Theorems.Thm_OAI_Saxl_twoBand_support

-- ---- from OAI.RepresentationTheory.Saxl.Basic ----
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
/- The coefficient of the canonical row word in its polytabloid is one. -/
/- The staircase has triangular cardinality. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.HighProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/
/- Local same-high projection in the ordinary pair-letter coordinate space. -/
/- Move low row letters to the band and high row letters to B_h. -/
lemma rotateRow_high (h s : ℕ) (x : (staircase (h+s)).cells) :
    s ≤ (rotateRow h s x).val.2 ↔ x.val.1 + x.val.2 < h := by
  have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
  change s ≤ (if x.val.2 < h - x.val.1 then x.val.2+s else x.val.2-(h-x.val.1)) ↔ _
  split_ifs <;> omega

lemma rotateColumn_high (h s : ℕ) (x : (staircase (h+s)).cells) :
    s ≤ (rotateColumn h s x).val.1 ↔ x.val.1 + x.val.2 < h := by
  have hh := rotateRow_high h s (staircaseSwap (h+s) x)
  change s ≤ (rotateRow h s (staircaseSwap (h+s) x)).val.2 ↔ _
  simpa [staircaseSwap, Nat.add_comm] using hh

/- The projected generator is genuinely nonzero for every band width,
without assuming a tensor factorization. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.CoordinateSector ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/
/- Permutations preserving a position sector. -/
/- The genuine unnormalized signed block alternation. -/
/- Keeping a prescribed coloring restricts the alternating group to its
sector stabilizer. This is the finite coset calculation behind block-factorization. -/
end Saxl

namespace Saxl
/- The prescribed high sector in the actual staircase enumeration. -/
lemma polytabloid_eq_altWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t = altWord (columnGroup t) (rowWord t) := rfl

/- The cut's two layers, with their exact retained row and column permutations. -/
/- Exact sign cancellation in the two retained layers. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.PositionSplit ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl
/- The genuine product position permutation under a disjoint-set enumeration. -/
lemma signC_sumPerm {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
    signC (sumPerm e g h) = signC g * signC h := by
  simp [signC_def, sumPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

lemma word_eq_iff_parts {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w v : Fin n → Fin d) : w = v ↔ leftWord e w = leftWord e v ∧ rightWord e w = rightWord e v := by
  constructor
  · rintro rfl; exact ⟨rfl,rfl⟩
  · rintro ⟨h₁,h₂⟩
    funext i
    obtain ⟨k, rfl⟩ := e.symm.surjective i
    cases k with
    | inl k => exact congrFun h₁ k
    | inr k => exact congrFun h₂ k

lemma single_positionProduct {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w : Fin n → Fin d) :
    (Pi.single w (1:ℂ) : WordSpace n d) =
      positionProduct e (Pi.single (leftWord e w) 1) (Pi.single (rightWord e w) 1) := by
  classical
  ext v
  simp only [positionProduct, Pi.single_apply]
  simp only [word_eq_iff_parts e]
  split_ifs <;> simp_all

lemma altWord_split_term {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w v : Fin n → Fin d) (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
    (signC (sumPerm e g h) • wordRep n d (sumPerm e g h) (Pi.single w 1)) v =
    (signC g • wordRep a d g (Pi.single (leftWord e w) 1)) (leftWord e v) *
      (signC h • wordRep b d h (Pi.single (rightWord e w) 1)) (rightWord e v) := by
  rw [single_positionProduct e w]
  change signC (sumPerm e g h) *
    ((Pi.single (leftWord e w) (1:ℂ) : WordSpace a d) (leftWord e (v ∘ sumPerm e g h)) *
      (Pi.single (rightWord e w) (1:ℂ) : WordSpace b d) (rightWord e (v ∘ sumPerm e g h))) = _
  have h₁ : leftWord e (v ∘ sumPerm e g h) = leftWord e v ∘ g := by
    ext i; simp [leftWord]
  have h₂ : rightWord e (v ∘ sumPerm e g h) = rightWord e v ∘ h := by
    ext i; simp [rightWord]
  rw [h₁,h₂,signC_sumPerm]
  change _ = (signC g * (Pi.single (leftWord e w) (1:ℂ) : WordSpace a d) (leftWord e v ∘ g)) *
    (signC h * (Pi.single (rightWord e w) (1:ℂ) : WordSpace b d) (rightWord e v ∘ h))
  ring

/- Independent block permutations factor with exactly the product sign. -/
theorem altWord_split {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (G : Subgroup (Equiv.Perm (Fin n))) (G₁ : Subgroup (Equiv.Perm (Fin a)))
    (G₂ : Subgroup (Equiv.Perm (Fin b))) (E : G ≃ G₁ × G₂)
    (hE : ∀ g : G, (g : Equiv.Perm (Fin n)) =
      sumPerm e ((E g).1 : Equiv.Perm (Fin a)) ((E g).2 : Equiv.Perm (Fin b)))
    (w : Fin n → Fin d) :
    altWord G w = positionProduct e (altWord G₁ (leftWord e w)) (altWord G₂ (rightWord e w)) := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite G₁
  let := Fintype.ofFinite G₂
  ext v
  unfold altWord
  simp only [Finset.sum_apply, positionProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : G₁ × G₂,
      (signC (p.1 : Equiv.Perm (Fin a)) • wordRep a d p.1 (Pi.single (leftWord e w) 1)) (leftWord e v) *
      (signC (p.2 : Equiv.Perm (Fin b)) • wordRep b d p.2 (Pi.single (rightWord e w) 1)) (rightWord e v) := by
        apply Fintype.sum_equiv E
        intro g
        rw [hE g]
        exact altWord_split_term e w v _ _
    _ = _ := Fintype.sum_prod_type _

/- Exact independent-block factorization for arbitrary row/column labels. -/
theorem altWord_fiber_split {n a b d : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin a ⊕ Fin b)
    (f : Fin n → α) (w : Fin n → Fin d) :
    altWord (fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true)) w =
      positionProduct e
        (altWord (fiberGroup (fun i => f (e.symm (Sum.inl i)))) (leftWord e w))
        (altWord (fiberGroup (fun i => f (e.symm (Sum.inr i)))) (rightWord e w)) := by
  apply altWord_split e _ _ _ (fiberSplit e f).symm
  intro g
  exact (congrArg Subtype.val ((fiberSplit e f).apply_symm_apply g)).symm

end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.BandFactorization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma cutPositions_left (h s : ℕ) (i : Fin (staircase h).card) :
    (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val = (stairTableau h i).val := by
  classical
  simp [cutPositions, Equiv.sumCompl, highPositionsEquiv]

lemma letterLift_single {n d e : ℕ} (f : Fin d → Fin e) (a : Fin n → Fin d) :
    letterLift f (Pi.single a 1) = Pi.single (f ∘ a) (1:ℂ) := by
  classical
  ext b
  rw [letterLift, wordMap_single, Pi.single_apply]
  by_cases he : b = f ∘ a
  · subst b; simp
  · rw [ite_eq_right he]
    have hn : ∃ i, f (a i) ≠ b i := by
      by_contra hh
      push Not at hh
      exact he (funext (fun i => (hh i).symm))
    obtain ⟨i,hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma letterLift_altWord {n d e : ℕ} (f : Fin d → Fin e)
    (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n → Fin d) :
    letterLift f (altWord G a) = altWord G (f ∘ a) := by
  classical
  unfold altWord
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [map_smul, Representation.IntertwiningMap.isIntertwining, letterLift_single]

lemma row_cut_group (h s : ℕ) :
    columnGroup (stairRowTableau (h+s)) ⊓ sectorGroup (stairHigh h s) =
      fiberGroup (fun i => (stairTableau (h+s) i).val.1) ⊓
        sectorGroup (fun i => (cutPositions h s i).isLeft = true) := by
  congr 1
  congr 1; funext i; exact propext (cutPositions_high h s i).symm

lemma column_cut_group (h s : ℕ) :
    columnGroup (stairTableau (h+s)) ⊓ sectorGroup (stairHigh h s) =
      fiberGroup (fun i => (stairTableau (h+s) i).val.2) ⊓
        sectorGroup (fun i => (cutPositions h s i).isLeft = true) := by
  congr 1
  congr 1; funext i; exact propext (cutPositions_high h s i).symm

lemma highRow_word (h s : ℕ) :
    leftWord (cutPositions h s) (rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _)) =
      highLetter h s ∘ rowWord (stairRowTableau h) := by
  funext i
  apply Fin.ext
  have hi : (stairTableau h i).val.1 + (stairTableau h i).val.2 < h :=
    mem_staircase.mp (stairTableau h i).property
  have he := cutPositions_left h s i
  simp only [leftWord, Function.comp_apply, rowWord, stairRowTableau, rotateRowPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply, staircaseSwap, highLetter]
  change (rotateRow h s (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i)))).val.2 = _
  change (if _ then _ else _) = (stairTableau h i).val.2+s
  rw [he]
  rw [ite_eq_left (by omega)]

lemma highColumn_word (h s : ℕ) :
    leftWord (cutPositions h s) (rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _)) =
      highLetter h s ∘ rowWord (stairTableau h) := by
  funext i
  apply Fin.ext
  have hi : (stairTableau h i).val.1 + (stairTableau h i).val.2 < h :=
    mem_staircase.mp (stairTableau h i).property
  have he := cutPositions_left h s i
  simp only [leftWord, Function.comp_apply, rowWord, rotateColumnPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply, highLetter]
  change (rotateColumn h s (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i)))).val.1 = _
  change (if (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.1 <
      h - (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.2 then
      (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.1+s else
      (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.1 -
        (h - (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.2)) = _
  simp only [he]
  rw [ite_eq_left (by omega)]

/- The first-layer exact band factorization, including the high-letter shift. -/
theorem cutRowWord_factor (h s : ℕ) : cutRowWord h s =
    positionProduct (cutPositions h s)
      (letterLift (highLetter h s) (polytabloid (stairRowTableau h))) (bandRowWord h s) := by
  unfold cutRowWord
  rw [row_cut_group, altWord_fiber_split]
  congr 1
  rw [highRow_word, polytabloid_eq_altWord, letterLift_altWord]
  congr 1
  change fiberGroup _ = fiberGroup (fun i => (stairTableau h i).val.1)
  congr 1
  funext i
  exact congrArg Prod.fst (cutPositions_left h s i)

/- The second-layer exact band factorization. -/
theorem cutColumnWord_factor (h s : ℕ) : cutColumnWord h s =
    positionProduct (cutPositions h s)
      (letterLift (highLetter h s) (polytabloid (stairTableau h))) (bandColumnWord h s) := by
  unfold cutColumnWord
  rw [column_cut_group, altWord_fiber_split]
  congr 1
  rw [highColumn_word, polytabloid_eq_altWord, letterLift_altWord]
  congr 1
  change fiberGroup _ = fiberGroup (fun i => (stairTableau h i).val.2)
  congr 1
  funext i
  exact congrArg Prod.snd (cutPositions_left h s i)

/- The exact path order, starting at the bottom row singleton and ending
at the rightmost column singleton. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.CyclicSector ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

/- Explicit finite-group induction on a linear map. -/
/- Coordinate-sector induction, in precisely the nonzero-Hom form used in
the staircase induction. The projector kills translates outside the stabilizer. -/
open scoped MonoidAlgebra

theorem intertwining_lift_surjective {G : Type uG} {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (hF : Function.Surjective F)
    (f : Representation.IntertwiningMap τ σ) :
    ∃ h : Representation.IntertwiningMap τ ρ, F.comp h = f := by
  let EF := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
  let EH := Representation.IntertwiningMap.equivLinearMapAsModule τ ρ
  let Ef := Representation.IntertwiningMap.equivLinearMapAsModule τ σ
  obtain ⟨h, hh⟩ := IsSemisimpleModule.lifting_property (EF F) hF (Ef f)
  refine ⟨EH.symm h, ?_⟩
  ext z
  exact LinearMap.congr_fun hh z

end Saxl

namespace Saxl

/- Concrete sector averaging produces a constituent of the full cyclic
module from an equivariant map on its coordinate sector. -/
lemma cyclicMap_surjective {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (v : X) : Function.Surjective (cyclicMap F v) := by
  intro y
  have hy := y.property
  change y.val ∈ Submodule.span ℂ _ at hy
  suffices ∃ x : (cyclic ρ v).toSubmodule, (cyclicMap F v x).val = y.val by
    obtain ⟨x,hx⟩ := this
    exact ⟨x,Subtype.ext hx⟩
  generalize hz : y.val = z at hy ⊢
  clear y hz
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g,rfl⟩ := hz
    refine ⟨(cyclic ρ v).toRepresentation g ⟨v,mem_cyclic _ _⟩, ?_⟩
    change F (ρ g v) = σ g (F v)
    exact LinearMap.congr_fun (F.isIntertwining' g) v
  | zero => exact ⟨0,map_zero F⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨u,hu⟩ := ihx
    obtain ⟨w,hw⟩ := ihy
    refine ⟨u+w, ?_⟩
    change F (u.val+w.val) = _
    rw [map_add,show F u.val = x from hu,show F w.val = y from hw]
  | smul c x hx ih =>
    obtain ⟨u,hu⟩ := ih
    refine ⟨c • u, ?_⟩
    change F (c • u.val) = _
    rw [map_smul,show F u.val = x from hu]

/- A genuine equivariant projection of a cyclic generator transfers every
nonzero constituent map back to the original cyclic module by Maschke. -/
theorem cyclic_projection_support {G : Type uG} {X : Type uX} {Y : Type uY} {Z : Type uZ} [Group G] [Finite G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (v : X)
    (f : Representation.IntertwiningMap τ (cyclic σ (F v)).toRepresentation) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap τ (cyclic ρ v).toRepresentation, g ≠ 0 := by
  obtain ⟨g,hg⟩ := intertwining_lift_surjective (cyclicMap F v) (cyclicMap_surjective F v) f
  refine ⟨g, ?_⟩
  intro hz
  apply hf
  rw [← hg,hz]
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact map_zero (cyclicMap F v)

end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.BandSupport ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Every Specht shape with at most four rows occurs in the cyclic module
generated by the prescribed two-band vector. -/
end Saxl

namespace Saxl

/- Coordinate subrepresentation using only letters with property A. -/
lemma alphabetSub_iff {n d : ℕ} (A : Fin d → Prop) (x : WordSpace n d) :
    x ∈ alphabetSub n d A ↔ ∀ w, x w ≠ 0 → ∀ i, A (w i) := by
  change (∀ w, (∃ i, ¬ A (w i)) → x w = 0) ↔ _
  constructor
  · intro h w hw i
    by_contra hn
    exact hw (h w ⟨i,hn⟩)
  · intro h w hw
    by_contra hn
    obtain ⟨i,hi⟩ := hw
    exact hi (h w hn i)

lemma single_mem_alphabet {n d : ℕ} (A : Fin d → Prop) (a : Fin n → Fin d) (ha : ∀ i, A (a i)) :
    (Pi.single a (1:ℂ) : WordSpace n d) ∈ alphabetSub n d A := by
  classical
  intro w hw
  apply Pi.single_eq_of_ne
  intro he
  subst w
  obtain ⟨i,hi⟩ := hw
  exact hi (ha i)

lemma altWord_mem_alphabet {n d : ℕ} (A : Fin d → Prop)
    (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n → Fin d) (ha : ∀ i, A (a i)) :
    altWord G a ∈ alphabetSub n d A := by
  classical
  unfold altWord
  apply Submodule.sum_mem
  intro g hg
  apply Submodule.smul_mem
  exact (alphabetSub n d A).apply_mem_toSubmodule g.val (single_mem_alphabet A a ha)

lemma letterLift_mem_alphabet {n d D : ℕ} (A : Fin D → Prop)
    (φ : Fin d → Fin D) (hφ : ∀ i, A (φ i)) (x : WordSpace n d) :
    letterLift φ x ∈ alphabetSub n D A := by
  classical
  intro w hw
  obtain ⟨i,hi⟩ := hw
  change (∑ a, x a * ∏ j, (if φ (a j) = w j then (1:ℂ) else 0)) = 0
  apply Finset.sum_eq_zero
  intro a ha
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact ite_eq_right (fun hh : φ (a i) = w i => hi (hh ▸ hφ (a i)))

lemma pairLift_wordTensor {n d D : ℕ} (φ : Fin d → Fin D) (x y : WordSpace n d) :
    pairLift φ (wordTensor n d d (x ⊗ₜ[ℂ] y)) =
      wordTensor n D D (letterLift φ x ⊗ₜ[ℂ] letterLift φ y) := by
  let E := (wordTensorIntertwiner n d d).ofBijective (wordTensor n d d).bijective
  change wordTensor n D D (((letterLift φ).tensor (letterLift φ)) (E.symm (E (x ⊗ₜ[ℂ] y)))) = _
  rw [E.symm_apply_apply]
  rfl

lemma pairWord_mem_alphabetLeft {n d : ℕ} (A : Fin d → Prop)
    (x y : WordSpace n d) (hx : x ∈ alphabetSub n d A) :
    wordTensor n d d (x ⊗ₜ[ℂ] y) ∈
      alphabetSub n (d*d) (fun a => A (finProdFinEquiv.symm a).1) := by
  apply (alphabetSub_iff _ _).mpr
  intro w hw i
  rw [wordTensor_tmul] at hw
  exact (alphabetSub_iff A x).mp hx (splitLeft w) ((mul_ne_zero_iff.mp hw).1) i

lemma shiftedStairWord_alphabet (h s : ℕ) :
    shiftedStairWord h s ∈ alphabetSub _ _ (fun a => s ≤ ((finProdFinEquiv.symm a).1).val) := by
  unfold shiftedStairWord staircaseWord
  rw [pairLift_wordTensor]
  apply pairWord_mem_alphabetLeft (fun a => s ≤ a.val)
  apply letterLift_mem_alphabet
  intro i
  dsimp [highLetter]
  omega

lemma bandRowWord_alphabet (h s : ℕ) :
    bandRowWord h s ∈ alphabetSub _ _ (fun a => ¬s ≤ a.val) := by
  apply altWord_mem_alphabet
  intro j
  have hb := (bandTableau_bounds h s j).1
  have hr := rotateRow_high h s (bandTableau h s j)
  have hh : ¬ s ≤ (rotateRow h s (bandTableau h s j)).val.2 :=
    fun hh => (Nat.not_lt.mpr hb) (hr.mp hh)
  simpa [rightWord,rowWord,stairRowTableau,rotateRowPositions,bandTableau,staircaseSwap] using hh

lemma stairBandWord_alphabet (h s : ℕ) :
    stairBandWord h s ∈ alphabetSub _ _ (fun a => ¬ s ≤ ((finProdFinEquiv.symm a).1).val) := by
  apply pairWord_mem_alphabetLeft (fun a => ¬s ≤ a.val)
  exact bandRowWord_alphabet h s

/- The actual same-high image factors as the smaller Specht tensor cyclic
vector and the exact retained band vector on independent position blocks. -/
theorem staircase_cut_factor (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) =
      positionProduct (cutPositions h s) (shiftedStairWord h s) (stairBandWord h s) := by
  rw [staircase_cut_layers,cutRowWord_factor,cutColumnWord_factor]
  unfold shiftedStairWord staircaseWord
  rw [pairLift_wordTensor]
  ext w
  simp only [wordTensor_tmul, stairBandWord, positionProduct]
  exact mul_mul_mul_comm _ _ _ _

lemma bandColumnWord_alphabet (h s : ℕ) :
    bandColumnWord h s ∈ alphabetSub _ _ (fun a => ¬s ≤ a.val) := by
  apply altWord_mem_alphabet
  intro j
  have hb := (bandTableau_bounds h s j).1
  have hr := rotateColumn_high h s (bandTableau h s j)
  have hh : ¬ s ≤ (rotateColumn h s (bandTableau h s j)).val.1 :=
    fun hh => (Nat.not_lt.mpr hb) (hr.mp hh)
  simpa [rightWord,rowWord,rotateColumnPositions,bandTableau] using hh

lemma alphabet_small_invariant {n d : ℕ} (A : Fin d → Prop)
    (hA : ∀ a b, A a → A b → a = b) (x : WordSpace n d)
    (hx : x ∈ alphabetSub n d A) (g : Equiv.Perm (Fin n)) : wordRep n d g x = x := by
  ext w
  change x (w ∘ g) = x w
  have he : (∀ i, A (w i)) → w ∘ g = w := by
    intro h
    funext i
    exact hA _ _ (h (g i)) (h i)
  by_cases h : ∀ i, A (w i)
  · rw [he h]
  · have hz : x w = 0 := by
      by_contra hn
      exact h ((alphabetSub_iff A x).mp hx w hn)
    rw [hz]
    by_contra hn
    have hh := (alphabetSub_iff A x).mp hx (w ∘ g) hn
    apply h
    intro i
    simpa using hh (g⁻¹ i)

lemma oneBand_invariant (h : ℕ) (g : Equiv.Perm (Fin (bandSize h 1))) :
    wordRep _ _ g (stairBandWord h 1) = stairBandWord h 1 := by
  have ha (a b : Fin ((staircase (h+1)).colLen 0)) (ha : ¬1 ≤ a.val) (hb : ¬1 ≤ b.val) : a = b := by
    apply Fin.ext; omega
  have hr := alphabet_small_invariant (fun a => ¬1 ≤ a.val) ha _ (bandRowWord_alphabet h 1) g
  have hc := alphabet_small_invariant (fun a => ¬1 ≤ a.val) ha _ (bandColumnWord_alphabet h 1) g
  ext w
  change stairBandWord h 1 (w ∘ g) = stairBandWord h 1 w
  simp only [stairBandWord,wordTensor_tmul]
  exact congrArg₂ (fun x y : ℂ => x*y) (congrFun hr (splitLeft w)) (congrFun hc (splitRight w))

lemma stairBandWord_ne_zero (h s : ℕ) : stairBandWord h s ≠ 0 := by
  intro hz
  apply staircase_projected_ne_zero h s
  rw [staircase_cut_factor,hz]
  ext w
  change _ * 0 = 0
  exact mul_zero _

lemma oneRow_support_invariant {n d : ℕ} (μ : YoungDiagram) (t : Tableau n μ)
    (hμ : μ.colLen 0 ≤ 1) (u : WordSpace n d) (hu : u ≠ 0)
    (he : ∀ g, wordRep n d g u = u) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, f ≠ 0 := by
  have hw (g : Equiv.Perm (Fin n)) : rowWord t ∘ g = rowWord t := by
    funext i
    apply Fin.ext
    have h₁ := (rowWord t (g i)).isLt
    have h₂ := (rowWord t i).isLt
    omega
  let F : Specht t →ₗ[ℂ] (cyclic (wordRep n d) u).toSubmodule :=
    { toFun := fun x => ⟨x.val (rowWord t) • u, Submodule.smul_mem _ _ (mem_cyclic _ _)⟩
      map_add' := by intro x y; apply Subtype.ext; exact add_smul _ _ _
      map_smul' := by intro c x; apply Subtype.ext; exact mul_smul _ _ _ }
  let f : Representation.IntertwiningMap (spechtRep t) (cyclic (wordRep n d) u).toRepresentation :=
    { toLinearMap := F
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        change x.val (rowWord t ∘ g) • u = wordRep n d g (x.val (rowWord t) • u)
        rw [hw,map_smul,he] }
  refine ⟨f, ?_⟩
  intro hz
  have hh := congrArg (fun f => (f ⟨polytabloid t,mem_cyclic _ _⟩).val) hz
  change polytabloid t (rowWord t) • u = 0 at hh
  rw [polytabloid_rowWord,one_smul] at hh
  exact hu hh

/- The width-one band is the genuine trivial constituent required by Pieri. -/
theorem oneBand_support (h : ℕ) (μ : YoungDiagram) (t : Tableau (bandSize h 1) μ)
    (hμ : μ.colLen 0 ≤ 1) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep _ _) (stairBandWord h 1)).toRepresentation, f ≠ 0 :=
  oneRow_support_invariant μ t hμ _ (stairBandWord_ne_zero h 1) (oneBand_invariant h)

end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.HorizontalRemoval ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
lemma rowLen_zero_of_height_le (μ : YoungDiagram) {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  have hm := YoungDiagram.mem_iff_lt_rowLen.mpr h
  have hh := YoungDiagram.mem_iff_lt_colLen.mp hm
  omega

lemma rowPrefix_eq_card (μ : YoungDiagram) {k : ℕ} (hk : μ.colLen 0 ≤ k) :
    rowPrefix μ k = μ.card := by
  have he : μ.card = ∑ i : Fin (μ.colLen 0), μ.rowLen i := by
    have hh := Fintype.card_congr (rowCellEquiv μ)
    simpa using hh
  rw [he, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hk)
  intro i hik hin
  exact rowLen_zero_of_height_le μ (by simpa using hin)

/- Tallest-column bottom deletion, expressed by interlacing rows. -/
lemma rowPrefix_le_card (μ : YoungDiagram) (k : ℕ) : rowPrefix μ k ≤ μ.card := by
  rw [← rowPrefix_eq_card μ (Nat.le_max_left _ k)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_max_right _ _))

end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.CyclicTensor ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY

namespace Saxl

/- Positive Young rule as a concrete orbit map (including reordered contents). -/
unseal intertwiningLiftSubrep in
lemma intertwiningLiftSubrep_injective {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f)
    (S : Subrepresentation σ) (hS : S ≤ f.range) :
    Function.Injective (intertwiningLiftSubrep f hf S hS) := by
  intro x y h
  apply Subtype.ext
  have hh := (intertwiningRangeEquiv f hf).symm.injective h
  exact congrArg (fun z : f.range => (z : Y)) hh

-- [generator] dropped (set where defined): attribute [irreducible] intertwiningLiftSubrep

/- The genuine cyclic module is embedded in the actual staircase Specht square. -/
-- [generator] dropped (set where defined): attribute [irreducible] staircaseToTensor

lemma staircaseToTensor_injective (m : ℕ) : Function.Injective (staircaseToTensor m) := by
  unfold staircaseToTensor
  exact @intertwiningLiftSubrep_injective (Equiv.Perm (Fin (staircase m).card))
    (Specht (stairTableau m) ⊗[ℂ] Specht (stairTableau m))
    (WordSpace (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0))
    _ _ _ _ _
    ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m)))
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0))
    (staircaseTensorMap m) (staircaseTensorMap_injective m)
    (staircaseCyclic m) (staircaseCyclic_le_tensorRange m)

/- Every Specht type occurs in the specified staircase cyclic module. -/
/- A proof of cyclic support proves the original Kronecker-multiplicity target. -/
theorem saxl_of_cyclic_support (h : CyclicSaxlConjecture) : SaxlConjecture := by
  intro m hm μ hμ
  apply (kronecker_pos_iff _ _ _).mpr
  obtain ⟨f, hf⟩ := h m hm μ hμ
  refine ⟨(staircaseToTensor m).comp f, ?_⟩
  intro he
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply staircaseToTensor_injective m
  exact (congrArg (fun F : Representation.IntertwiningMap (spechtRep (canonicalTableau μ hμ))
      ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m))) => F x) he).trans
    (map_zero _).symm

end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.Main ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

lemma SizedStripChain.of_horizontal {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    SizedStripChain [μ.card-ν.card] ν μ := by
  have hc : ν.card ≤ μ.card := Finset.card_le_card hs.1
  exact SizedStripChain.snoc (SizedStripChain.nil ν) hs (Nat.add_sub_of_le hc)

lemma StripChain.sized {q ν μ} (hs : StripChain q ν μ) :
    ∃ bs : List ℕ, bs.length = q ∧ SizedStripChain bs ν μ := by
  induction hs with
  | nil μ => exact ⟨[],rfl,SizedStripChain.nil μ⟩
  | @snoc q ν η μ hs hh hn ih =>
    obtain ⟨bs,hbs,hS⟩ := ih
    have hc : η.card ≤ μ.card := Finset.card_le_card hh.1
    exact ⟨bs++[μ.card-η.card], by simp [hbs], SizedStripChain.snoc hS hh (Nat.add_sub_of_le hc)⟩

/- Lift the factor support through the exact same-high quotient. -/
theorem band_cut_support (h s m : ℕ) (he : h+s=m)
    (ν μ : YoungDiagram) (hν : ν.card = (staircase h).card)
    (t : Tableau (staircase m).card μ) (bs : List ℕ) (hs : SizedStripChain bs ν μ)
    (fh : Representation.IntertwiningMap (spechtRep (canonicalTableau ν hν))
      (staircaseCyclic h).toRepresentation) (hfh : fh ≠ 0)
    (hband : ∀ (η : YoungDiagram) (r : Tableau (bandSize h s) η), η.colLen 0 ≤ bs.length →
      ∃ F : Representation.IntertwiningMap (spechtRep r)
        (cyclic (wordRep _ _) (stairBandWord h s)).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t) (staircaseCyclic m).toRepresentation, F ≠ 0 := by
  subst m
  obtain ⟨f,hf⟩ := shiftedStairWord_support h s ν (canonicalTableau ν hν) fh hfh
  have H := strip_product_support hs (canonicalTableau ν hν) t (cutPositions h s)
    (shiftedStairWord h s) (stairBandWord h s)
    (fun a => s ≤ ((finProdFinEquiv.symm a).1).val)
    (shiftedStairWord_alphabet h s) (stairBandWord_alphabet h s) f hf hband
  rw [← staircase_cut_factor] at H
  obtain ⟨F,hF⟩ := H
  exact cyclic_projection_support (sameHighProjection _ _ _ s) (staircaseWord (h+s)) F hF

lemma staircase_one_dominates (μ : YoungDiagram) (hμ : μ.card = (staircase 1).card) :
    Dominates (staircase 1) μ := by
  intro k
  by_cases hk : k=0
  · subst k; simp [rowPrefix]
  · have hh : (staircase 1).colLen 0 ≤ k := by simp only [staircase_colLen]; omega
    rw [rowPrefix_eq_card _ hh,← hμ]
    exact rowPrefix_le_card μ k

/- Strong induction, including m=1 and every
partition of the exact triangular size. -/
theorem full_cyclic_support (m : ℕ) (hm : 1 ≤ m) (μ : YoungDiagram)
    (t : Tableau (staircase m).card μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep t) (staircaseCyclic m).toRepresentation, F ≠ 0 := by
  induction m using Nat.strong_induction_on generalizing μ with
  | h m ih =>
    have hμ : μ.card = (staircase m).card := by
      simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr t).symm
    by_cases hd : Dominates (staircase m) μ
    · exact dominated_support m hm μ t hd
    have hm2 : 2 ≤ m := by
      by_contra hn
      have he : m=1 := by omega
      subst m
      exact hd (staircase_one_dominates μ hμ)
    rcases strip_reduction m hm2 μ hμ hd with ⟨ν,hν,hs⟩ | ⟨hm5,q,hq,ν,hν,hs⟩
    · obtain ⟨f,hf⟩ := ih (m-1) (by omega) (by omega) ν (canonicalTableau ν hν)
      exact band_cut_support (m-1) 1 m (by omega) ν μ hν t [μ.card-ν.card]
        (SizedStripChain.of_horizontal hs) f hf (fun η r hη => oneBand_support (m-1) η r hη)
    · obtain ⟨f,hf⟩ := ih (m-2) (by omega) (by omega) ν (canonicalTableau ν hν)
      obtain ⟨bs,hbs,hS⟩ := hs.sized
      exact band_cut_support (m-2) 2 m (by omega) ν μ hν t bs hS f hf
        (fun η r hη => twoBand_support (m-2) (by omega) η r (by omega))

/- The strengthened cyclic form of Saxl’s conjecture. -/
theorem cyclic_saxl_conjecture : CyclicSaxlConjecture := by
  intro m hm μ hμ
  exact full_cyclic_support m hm μ (canonicalTableau μ hμ)

/- Every complex staircase tensor square contains
all Specht irreducibles of its symmetric group. -/
theorem saxl_conjecture : SaxlConjecture := saxl_of_cyclic_support cyclic_saxl_conjecture

/- Specht classification implies that every finite-dimensional irreducible
complex representation embeds in the staircase tensor square. -/
/- The positive-multiplicity conclusion with the literal
triangular degree, rather than the definitionally convenient cell count. -/
end Saxl

end

end OAI

-- ---- mission target ----
open OAI OAI.Saxl
open scoped TensorProduct
universe uG uV

namespace OAI
namespace Saxl
theorem _root_.solution : SaxlConjecture := by
  first
    | exact OAI.Saxl.saxl_conjecture
    | (apply OAI.Saxl.saxl_conjecture <;> assumption)
    | (intros; apply OAI.Saxl.saxl_conjecture <;> assumption)
end Saxl
end OAI
