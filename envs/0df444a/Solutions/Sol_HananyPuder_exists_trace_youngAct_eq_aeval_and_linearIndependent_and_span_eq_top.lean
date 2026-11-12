-- Prove2me | solution 1 for HananyPuder.exists_trace_youngAct_eq_aeval_and_linearIndependent_and_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:42:34.485901+00:00
-- url     : https://prove2.me/submissions/b751e2bc-e1d6-4e5c-8b80-47e199f8eb11

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Theorems.Thm_OAI_Saxl_specht_irreducible
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4
import Theorems.Thm_StrongConv_exists_linearEquiv_youngSpace_specht
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
import Theorems.Thm_HananyPuder_exists_trace_youngAct_eq_aeval_and_weightedTotalDegree_le
universe uX uV uW

section
/-!
# Shape rigidity of Specht modules and orthonormality of their characters

Ported (credited) from openai/math `lean/OAI/RepresentationTheory/Saxl/{Basic,Polytabloid,
SpechtSubmodule,ShapeRigidity,SpechtClassification}.lean`: Specht modules of different shapes
are inequivalent (James, *The representation theory of the symmetric groups*, Thm 4.12), hence the
characters of the Specht modules of the partitions of `n` are orthonormal.
-/

namespace HananyPuder.W2HP.PartR

open OAI OAI.Saxl

noncomputable section


lemma finset_eq_of_signed_sum {X : Type uX} [DecidableEq X]
    (A B : Finset X) (w : X → ℤ)
    (hp : ∀ x ∈ B, 0 < w x) (hn : ∀ x ∉ B, w x < 0)
    (he : ∑ x ∈ A, w x = ∑ x ∈ B, w x) : A = B := by
  classical
  let f := fun x => if x ∈ A then w x else 0
  let g := fun x => if x ∈ B then w x else 0
  have hle : ∀ x ∈ A ∪ B, f x ≤ g x := by
    intro x hx
    dsimp [f, g]
    split_ifs with ha hb hb
    · rfl
    · exact (hn x hb).le
    · exact (hp x hb).le
    · rfl
  have hs : ∑ x ∈ A ∪ B, f x = ∑ x ∈ A ∪ B, g x := by
    simpa [f, g, ← Finset.sum_filter] using he
  have hh := (Finset.sum_eq_sum_iff_of_le hle).mp hs
  ext x
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B
  · simp [ha, hb]
  · have hx := hh x (Finset.mem_union_left B ha)
    have hneg := hn x hb
    simp [f, g, ha, hb] at hx
    omega
  · have hx := hh x (Finset.mem_union_right A hb)
    have hpos := hp x hb
    simp [f, g, ha, hb] at hx
    omega
  · simp [ha, hb]

theorem column_perm_rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : columnGroup t) (hg : rowWord t ∘ (g : Equiv.Perm (Fin n)) = rowWord t) :
    g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply t.injective
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Fin.val (congrFun hg i)
  · exact g.property i

theorem polytabloid_rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t (rowWord t) = 1 := by
  classical
  unfold polytabloid
  simp only [Finset.sum_apply, Pi.smul_apply, wordRep, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  rw [Finset.sum_eq_single (1 : columnGroup t)]
  · simp
  · intro b hb hb1
    have hn : rowWord t ∘ (b : Equiv.Perm (Fin n)) ≠ rowWord t :=
      fun h => hb1 (column_perm_rowWord t b h)
    simp [hn]
  · simp

lemma columnAlt_mul {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    columnAlt (d := d) t * wordRep n d (h : Equiv.Perm (Fin n)) =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulRight h) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC (h : Equiv.Perm (Fin n)) •
    signC ((g * h : columnGroup t) : Equiv.Perm (Fin n)) •
      wordRep n d ((g * h : columnGroup t) : Equiv.Perm (Fin n)) = _
  simp only [Subgroup.coe_mul, map_mul, smul_smul]
  congr 1
  calc signC (h : Equiv.Perm (Fin n)) *
      (signC (g : Equiv.Perm (Fin n)) * signC (h : Equiv.Perm (Fin n))) =
      signC (g : Equiv.Perm (Fin n)) *
        (signC (h : Equiv.Perm (Fin n)) * signC (h : Equiv.Perm (Fin n))) := by ring
    _ = signC (g : Equiv.Perm (Fin n)) := by rw [signC_mul_self, mul_one]

lemma columnAlt_row {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    columnAlt t (Pi.single (rowWord t) 1) = polytabloid t := by
  simp [columnAlt, polytabloid, LinearMap.sum_apply]

lemma columnAlt_collision {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (i j : Fin n) (hij : i ≠ j)
    (hc : (t i).val.2 = (t j).val.2) (ha : a i = a j) :
    columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
  classical
  let h : columnGroup t :=
    ⟨Equiv.swap i j, fun k => Equiv.apply_swap_eq_self (v := fun l => (t l).val.2) hc k⟩
  have hs : signC (h : Equiv.Perm (Fin n)) = -1 := by
    simp [h, signC_def, Equiv.Perm.sign_swap hij]
  have hf : wordRep n d (h : Equiv.Perm (Fin n)) (Pi.single a 1) = Pi.single a 1 := by
    rw [wordRep_single]
    congr 1
    funext k
    exact Equiv.apply_swap_eq_self ha k
  have hh := congrArg (fun f : Module.End ℂ (WordSpace n d) => f (Pi.single a 1))
    (columnAlt_mul (d := d) t h)
  simp only [Module.End.mul_apply, hf, LinearMap.smul_apply, hs, neg_one_smul] at hh
  ext b
  exact CharZero.eq_neg_self_iff.mp (congrFun hh b)

lemma columnAlt_mem {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (P : Subrepresentation (wordRep n d)) {x : WordSpace n d} (hx : x ∈ P) :
    columnAlt t x ∈ P := by
  classical
  unfold columnAlt
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ (fun g _ =>
    Submodule.smul_mem _ _ (P.apply_mem_toSubmodule (g : Equiv.Perm (Fin n)) hx))

lemma spechtSub_le_tabloidSub {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    spechtSub t ≤ tabloidSub t := by
  apply (cyclic_le _ _ _).mpr
  rw [← columnAlt_row]
  exact columnAlt_mem t (tabloidSub t) (mem_cyclic _ _)

lemma columnAlt_pair {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (x y : WordSpace n d) :
    dotProduct (columnAlt t x) y = dotProduct x (columnAlt t y) := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, wordPair_move]
  apply (Equiv.sum_comp (Equiv.inv (columnGroup t)) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  simp only [Equiv.inv_apply, Subgroup.coe_inv, signC_inv, inv_inv]

lemma columnAlt_coefficient {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (x : WordSpace n (μ.colLen 0)) :
    columnAlt t x (rowWord t) = dotProduct x (polytabloid t) := by
  classical
  rw [← dotProduct_single_one (columnAlt t x), columnAlt_pair, columnAlt_row]

lemma polytabloid_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t ≠ 0 := by
  intro h
  have hh := congrFun h (rowWord t)
  rw [polytabloid_rowWord] at hh
  exact one_ne_zero hh

lemma tableau_image {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Finset.univ.image (fun i : Fin n => (t i).val) = μ.cells := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact (t i).property
  · intro hx; exact ⟨t.symm ⟨x, hx⟩, by simp⟩

lemma tableau_sum {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (f : ℕ × ℕ → ℤ) :
    ∑ i, f (t i).val = ∑ c ∈ μ.cells, f c := by
  classical
  conv_rhs => rw [← tableau_image t]
  rw [Finset.sum_image]
  intro i hi j hj h
  exact t.injective (Subtype.val_injective h)

lemma finset_signed_sum_le {X : Type uX} [DecidableEq X]
    (A B : Finset X) (w : X → ℤ)
    (hp : ∀ x ∈ B, 0 ≤ w x) (hn : ∀ x ∉ B, w x ≤ 0) :
    ∑ x ∈ A, w x ≤ ∑ x ∈ B, w x := by
  classical
  have hle : ∀ x ∈ A ∪ B,
      (if x ∈ A then w x else 0) ≤ (if x ∈ B then w x else 0) := by
    intro x hx
    split_ifs with ha hb hb
    · rfl
    · exact hn x hb
    · exact hp x hb
    · rfl
  simpa [← Finset.sum_filter] using Finset.sum_le_sum hle

lemma mixed_moment_le {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν) (g : Equiv.Perm (Fin n))
    (hi : Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2))) :
    rowMoment μ ≤ rowMoment ν := by
  classical
  let f : Fin n → ℕ × ℕ := fun i => ((u (g i)).val.1, (t i).val.2)
  let w : ℕ × ℕ → ℤ := fun c => 2 * (μ.colLen c.2 : ℤ) - 2 * c.1 - 1
  have h := finset_signed_sum_le (Finset.univ.image f) μ.cells w
    (fun c hc => by have hh := YoungDiagram.mem_iff_lt_colLen.mp hc; dsimp [w]; omega)
    (fun c hc => by
      have hh : μ.colLen c.2 ≤ c.1 :=
        le_of_not_gt (fun h => hc (YoungDiagram.mem_iff_lt_colLen.mpr h))
      dsimp [w]; omega)
  rw [Finset.sum_image (fun _ _ _ _ h => hi h), ← tableau_sum t w] at h
  simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  rw [Equiv.sum_comp g (fun i => ((u i).val.1 : ℤ))] at h
  have ht := tableau_sum t (fun c => (c.1 : ℤ))
  have hu := tableau_sum u (fun c => (c.1 : ℤ))
  change _ = rowMoment μ at ht
  change _ = rowMoment ν at hu
  omega

lemma mixed_support_eq {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν) (g : Equiv.Perm (Fin n))
    (hi : Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2)))
    (hm : rowMoment μ = rowMoment ν) :
    Finset.univ.image (fun i => ((u (g i)).val.1, (t i).val.2)) = μ.cells := by
  classical
  let f : Fin n → ℕ × ℕ := fun i => ((u (g i)).val.1, (t i).val.2)
  let w : ℕ × ℕ → ℤ := fun c => 2 * (μ.colLen c.2 : ℤ) - 2 * c.1 - 1
  apply finset_eq_of_signed_sum _ _ w
    (fun c hc => by have hh := YoungDiagram.mem_iff_lt_colLen.mp hc; dsimp [w]; omega)
    (fun c hc => by
      have hh : μ.colLen c.2 ≤ c.1 :=
        le_of_not_gt (fun h => hc (YoungDiagram.mem_iff_lt_colLen.mpr h))
      dsimp [w]; omega)
  rw [Finset.sum_image (fun _ _ _ _ h => hi h), ← tableau_sum t w]
  simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Equiv.sum_comp g (fun i => ((u i).val.1 : ℤ))]
  have ht := tableau_sum t (fun c => (c.1 : ℤ))
  have hu := tableau_sum u (fun c => (c.1 : ℤ))
  change _ = rowMoment μ at ht
  change _ = rowMoment ν at hu
  rw [ht, hu, hm]

lemma rowLen_eq_count {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (r : ℕ) :
    μ.rowLen r = (Finset.univ.filter (fun i => (t i).val.1 = r)).card := by
  classical
  rw [YoungDiagram.rowLen_eq_card]
  have hf : μ.row r = (Finset.univ.filter (fun i => (t i).val.1 = r)).image
      (fun i => (t i).val) := by
    unfold YoungDiagram.row
    conv_lhs => rw [← tableau_image t]
    rw [Finset.filter_image]
  rw [hf, Finset.card_image_iff.mpr]
  intro i hi j hj h
  exact t.injective (Subtype.val_injective h)

lemma shapes_eq_of_mixed {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν) (g : Equiv.Perm (Fin n))
    (hi : Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2)))
    (hm : rowMoment μ = rowMoment ν) : μ = ν := by
  classical
  have hs := mixed_support_eq t u g hi hm
  have hrow : ∀ r, μ.rowLen r = ν.rowLen r := by
    intro r
    rw [YoungDiagram.rowLen_eq_card, YoungDiagram.row, ← hs,
      Finset.filter_image, Finset.card_image_iff.mpr (fun i _ j _ h => hi h),
      rowLen_eq_count u r]
    apply Finset.card_equiv g
    intro i
    simp
  apply YoungDiagram.ext
  ext c
  rcases c with ⟨r, s⟩
  change (r, s) ∈ μ ↔ (r, s) ∈ ν
  simp only [YoungDiagram.mem_iff_lt_rowLen, hrow]

lemma columnAlt_polytabloid_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    columnAlt t (polytabloid t) ≠ 0 := by
  intro hz
  have h := congrFun hz (rowWord t)
  rw [columnAlt_coefficient] at h
  change dotProduct (polytabloid t) (polytabloid t) = 0 at h
  conv at h => lhs; rhs; rw [← polytabloid_real t]
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact polytabloid_ne_zero t (dotProduct_self_star_eq_zero.mp h)

lemma mixed_injective_of_columnAlt_ne_zero {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν)
    {x : WordSpace n (ν.colLen 0)} (hx : x ∈ tabloidSub u)
    (hz : columnAlt t x ≠ 0) :
    ∃ g : Equiv.Perm (Fin n),
      Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2)) := by
  classical
  by_contra h
  push Not at h
  have hall : ∀ g : Equiv.Perm (Fin n),
      columnAlt t (wordRep n (ν.colLen 0) g (Pi.single (rowWord u) 1)) = 0 := by
    intro g
    have hh := h g⁻¹
    simp only [Function.Injective] at hh
    push Not at hh
    obtain ⟨i, j, he, hij⟩ := hh
    rw [wordRep_single]
    exact columnAlt_collision t _ i j hij (Prod.mk.inj he).2
      (Fin.ext (Prod.mk.inj he).1)
  apply hz
  clear hz
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hall g
  | zero => exact map_zero _
  | add y z hy hz ihy ihz => rw [map_add, ihy, ihz, add_zero]
  | smul c y hy ih => rw [map_smul, ih, smul_zero]

lemma columnOperator_intertwining {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) V}
    {σ : Representation ℂ (Equiv.Perm (Fin n)) W}
    (f : Representation.IntertwiningMap ρ σ) (x : V) :
    f (columnOperator t ρ x) = columnOperator t σ (f x) := by
  classical
  simp only [columnOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Representation.IntertwiningMap.isIntertwining]

lemma columnOperator_subtype {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (S : Subrepresentation (wordRep n d)) (x : S.toSubmodule) :
    (columnOperator t S.toRepresentation x).val = columnAlt t x.val := by
  let inc : Representation.IntertwiningMap S.toRepresentation (wordRep n d) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun g => rfl }
  exact columnOperator_intertwining t inc x

lemma mixed_injective_of_equiv {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν)
    (e : Representation.Equiv (spechtRep t) (spechtRep u)) :
    ∃ g : Equiv.Perm (Fin n),
      Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2)) := by
  let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
  apply mixed_injective_of_columnAlt_ne_zero t u
    (spechtSub_le_tabloidSub u (e p).property)
  intro hz
  have he := columnOperator_intertwining t e.toIntertwiningMap p
  have hy : columnOperator t (spechtRep u) (e p) = 0 := by
    apply Subtype.ext
    exact (columnOperator_subtype t (spechtSub u) (e p)).trans hz
  change e (columnOperator t (spechtRep t) p) = columnOperator t (spechtRep u) (e p) at he
  rw [hy] at he
  have ht : columnOperator t (spechtRep t) p = 0 := e.injective (he.trans (map_zero e).symm)
  have hh := congrArg Subtype.val ht
  exact columnAlt_polytabloid_ne_zero t
    ((columnOperator_subtype t (spechtSub t) p).symm.trans hh)

/-- Distinct Specht shapes are inequivalent (openai/math `specht_shape_rigidity`). -/
theorem specht_shape_rigidity {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν)
    (e : Representation.Equiv (spechtRep t) (spechtRep u)) : μ = ν := by
  obtain ⟨g, hg⟩ := mixed_injective_of_equiv t u e
  obtain ⟨h, hh⟩ := mixed_injective_of_equiv u t e.symm
  exact shapes_eq_of_mixed t u g hg
    (le_antisymm (mixed_moment_le t u g hg) (mixed_moment_le u t h hh))

lemma partitionDiagram_injective {n : ℕ} :
    Function.Injective (partitionDiagram (n := n)) := by
  intro p q h
  apply Nat.Partition.ext
  have he := congrArg (fun μ => (μ.rowLens : Multiset ℕ)) h
  simpa only [partitionDiagram_rowLens, Multiset.sort_eq] using he

/-- The character of the Specht module of a partition. -/
abbrev schar {n : ℕ} (p : Nat.Partition n) : Equiv.Perm (Fin n) → ℂ :=
  (spechtRep (partitionTableau p)).character

/-- The character scalar product against the Specht character of `q`. -/
def ip {n : ℕ} (f : Equiv.Perm (Fin n) → ℂ) (q : Nat.Partition n) : ℂ :=
  (Nat.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ * ∑ g, f g * schar q g⁻¹

lemma complex_card_ne_zero (G : Type*) [Group G] [Fintype G] : (Nat.card G : ℂ) ≠ 0 := by
  exact_mod_cast Nat.card_pos.ne'

/-- Orthonormality of the Specht characters. -/
lemma ip_schar {n : ℕ} (p q : Nat.Partition n) : ip (schar p) q = if p = q then 1 else 0 := by
  classical
  let : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (complex_card_ne_zero _)
  let := specht_irreducible (partitionTableau p)
  let := specht_irreducible (partitionTableau q)
  have h := Representation.char_orthonormal (spechtRep (partitionTableau p))
    (spechtRep (partitionTableau q))
  have he : Nonempty ((spechtRep (partitionTableau q)).Equiv
      (spechtRep (partitionTableau p))) ↔ p = q := by
    constructor
    · rintro ⟨e⟩
      exact (partitionDiagram_injective
        (specht_shape_rigidity (partitionTableau q) (partitionTableau p) e)).symm
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  unfold ip schar
  convert h using 1
  simp only [he]

lemma ip_add {n : ℕ} (f g : Equiv.Perm (Fin n) → ℂ) (q : Nat.Partition n) :
    ip (f + g) q = ip f q + ip g q := by
  simp only [ip, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

lemma ip_smul {n : ℕ} (c : ℂ) (f : Equiv.Perm (Fin n) → ℂ) (q : Nat.Partition n) :
    ip (c • f) q = c * ip f q := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

lemma ip_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Equiv.Perm (Fin n) → ℂ)
    (q : Nat.Partition n) : ip (∑ i ∈ s, f i) q = ∑ i ∈ s, ip (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ip_add, ih]

/-- The scalar product of a combination of Specht characters with `χ_q` picks out the
coefficients of the indices sent to `q`. -/
lemma ip_sum_schar {n : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℂ) (P : ι → Nat.Partition n)
    (q : Nat.Partition n) :
    ip (∑ i ∈ s, c i • schar (P i)) q = ∑ i ∈ s with P i = q, c i := by
  classical
  rw [ip_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ip_smul, ip_schar]
  simp

end

end HananyPuder.W2HP.PartR
end

section
/-!
# `youngSpace N (stableRows μ N)` as the Specht module of the partition `μ[N]`
-/

namespace HananyPuder.W2HP.PartB

open StrongConv OAI.Saxl

noncomputable section

/-- The representation of `S_N` on `youngSpace N rows`. -/
def youngRep (N : ℕ) (rows : List ℕ) :
    Representation ℂ (Equiv.Perm (Fin N)) (youngSpace N rows) where
  toFun σ := youngAct N rows σ
  map_one' := by
    ext x
    simp [youngAct]
  map_mul' σ τ := by
    ext x
    simp [youngAct, mul_assoc]

lemma youngEquivOfEq_aux {N : ℕ} :
    ∀ (c c' : MonoidAlgebra ℂ (Equiv.Perm (Fin N))) (_hc : c = c')
      (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin N)) V)
      (F : MonoidAlgebra ℂ (Equiv.Perm (Fin N)) → Type) [∀ c, AddCommGroup (F c)]
      [∀ c, Module ℂ (F c)] (R : ∀ c, Representation ℂ (Equiv.Perm (Fin N)) (F c)),
      Nonempty (ρ.Equiv (R c)) → Nonempty (ρ.Equiv (R c')) := by
  rintro c _ rfl V _ _ ρ F _ _ R h
  exact h

/-- Lists with the same Young symmetrizer give equivalent representations. -/
lemma youngEquivOfEq {N : ℕ} {L L' : List ℕ} (h : youngSymmetrizer N L = youngSymmetrizer N L') :
    Nonempty ((youngRep N L).Equiv (youngRep N L')) := by
  let F : MonoidAlgebra ℂ (Equiv.Perm (Fin N)) → Type := fun c =>
    (Submodule.span (MonoidAlgebra ℂ (Equiv.Perm (Fin N))) {c}).restrictScalars ℂ
  let R : ∀ c, Representation ℂ (Equiv.Perm (Fin N)) (F c) := fun c =>
    { toFun := fun σ => (LinearMap.mulLeft ℂ (MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) σ)).restrict
        (fun x hx => by
          rw [Submodule.restrictScalars_mem] at hx ⊢
          exact (Submodule.span _ {c}).smul_mem _ hx)
      map_one' := by ext x; simp
      map_mul' := fun σ τ => by ext x; simp [mul_assoc] }
  exact youngEquivOfEq_aux (youngSymmetrizer N L) (youngSymmetrizer N L') h _ (youngRep N L) F R
    ⟨Representation.Equiv.refl _⟩

lemma youngSymmetrizer_zero (L L' : List ℕ) : youngSymmetrizer 0 L = youngSymmetrizer 0 L' := by
  unfold youngSymmetrizer
  simp only [IsEmpty.forall_iff]

/-- The threshold `|μ| + μ₁ ≤ N`. -/
abbrev Thr (μ : YoungDiagram) (N : ℕ) : Prop := μ.cells.card + μ.rowLen 0 ≤ N

lemma stableRows_sortedGE (μ : YoungDiagram) (N : ℕ) (h : Thr μ N) :
    (stableRows μ N).SortedGE := by
  apply List.Pairwise.sortedGE
  rw [stableRows, List.pairwise_cons]
  refine ⟨fun a ha => ?_, (YoungDiagram.rowLens_sorted μ).pairwise⟩
  rw [YoungDiagram.rowLens, List.mem_map] at ha
  obtain ⟨i, _, rfl⟩ := ha
  have := μ.rowLen_anti 0 i (Nat.zero_le _)
  omega

lemma sum_filter_ne_zero' (L : List ℕ) : (L.filter (· ≠ 0)).sum = L.sum := by
  induction L with
  | nil => rfl
  | cons a L ih => by_cases ha : a = 0 <;> simp_all

lemma sum_rowLens (μ : YoungDiagram) : μ.rowLens.sum = μ.cells.card :=
  (card_eq_sum_rowLens μ).symm

/-- The partition `μ[N] = (N - |μ|, μ₁, μ₂, …)` of `N` (zero parts dropped, which only matters
for `N = 0`). -/
def stablePart (μ : YoungDiagram) (N : ℕ) (h : Thr μ N) : Nat.Partition N where
  parts := ((stableRows μ N).filter (· ≠ 0) : List ℕ)
  parts_pos := by
    intro i hi
    have := (List.mem_filter.mp (Multiset.mem_coe.mp hi)).2
    simp at this
    omega
  parts_sum := by
    rw [Multiset.sum_coe, sum_filter_ne_zero', stableRows, List.sum_cons, sum_rowLens]
    omega

lemma stableRows_ne_zero (μ : YoungDiagram) (N : ℕ) (h : Thr μ N) (hN : 0 < N) :
    ∀ a ∈ stableRows μ N, a ≠ 0 := by
  intro a ha
  rw [stableRows, List.mem_cons] at ha
  rcases ha with rfl | ha
  · by_contra h0
    have h1 : μ.rowLen 0 = 0 := by omega
    have h2 : μ.cells.card = 0 := by
      rw [← sum_rowLens, YoungDiagram.rowLens]
      have : μ.colLen 0 = 0 := by
        by_contra hc
        have hm : (0, 0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero hc)
        have := YoungDiagram.mem_iff_lt_rowLen.mp hm
        omega
      simp [this]
    omega
  · exact (μ.pos_of_mem_rowLens a ha).ne'

lemma rowLens_stablePart (μ : YoungDiagram) (N : ℕ) (h : Thr μ N) (hN : 0 < N) :
    (partitionDiagram (stablePart μ N h)).rowLens = stableRows μ N := by
  rw [partitionDiagram_rowLens]
  apply List.Perm.eq_of_sortedGE (Multiset.pairwise_sort _ _).sortedGE
    (stableRows_sortedGE μ N h)
  rw [← Multiset.coe_eq_coe, Multiset.sort_eq]
  change (((stableRows μ N).filter (· ≠ 0) : List ℕ) : Multiset ℕ) = _
  rw [List.filter_eq_self.mpr (fun a ha => by simpa using stableRows_ne_zero μ N h hN a ha)]

lemma youngSymmetrizer_stablePart (μ : YoungDiagram) (N : ℕ) (h : Thr μ N) :
    youngSymmetrizer N (stableRows μ N) =
      youngSymmetrizer N (partitionDiagram (stablePart μ N h)).rowLens := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact youngSymmetrizer_zero _ _
  · rw [rowLens_stablePart μ N h hN]

lemma card_eq_zero_bot (μ : YoungDiagram) (h : μ.cells.card = 0) : μ = ⊥ := by
  apply YoungDiagram.ext
  rw [Finset.card_eq_zero.mp h]
  rfl

lemma stablePart_injective {μ μ' : YoungDiagram} {N : ℕ} (h : Thr μ N) (h' : Thr μ' N)
    (he : stablePart μ N h = stablePart μ' N h') : μ = μ' := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [card_eq_zero_bot μ (by omega), card_eq_zero_bot μ' (by omega)]
  · have h1 := rowLens_stablePart μ N h hN
    rw [he, rowLens_stablePart μ' N h' hN, stableRows, stableRows] at h1
    have h2 := (List.cons.inj h1).2
    rw [← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := μ),
      ← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := μ')]
    congr 1
    exact h2.symm

/-- `youngSpace N (stableRows μ N)` is the Specht module of `μ[N]`. -/
theorem young_equiv_specht (μ : YoungDiagram) (N : ℕ) (h : Thr μ N) :
    Nonempty ((youngRep N (stableRows μ N)).Equiv
      (spechtRep (partitionTableau (stablePart μ N h)))) := by
  obtain ⟨e, he⟩ := exists_linearEquiv_youngSpace_specht (partitionTableau (stablePart μ N h))
  obtain ⟨e0⟩ := youngEquivOfEq (youngSymmetrizer_stablePart μ N h)
  refine ⟨e0.trans (Representation.Equiv.mk e (fun g => ?_))⟩
  exact LinearMap.ext fun x => he g x

end

end HananyPuder.W2HP.PartB
end

section
/-!
# Decomposition of a finite-dimensional representation of `S_n` into Specht modules

Maschke + `irreducible_equiv_specht`: every finite-dimensional complex representation of `S_n` is
equivalent to a product of Specht modules, and its character is the sum of their characters.
-/

namespace HananyPuder.W2HP.PartD

open OAI.Saxl Representation HananyPuder.W2HP.PartR

noncomputable section

variable {G : Type} [Group G]

/-- The product representation of a family of representations. -/
def piRep {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) : Representation ℂ G (∀ i, V i) where
  toFun g := LinearMap.pi (fun i => ρ i g ∘ₗ LinearMap.proj i)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp] lemma piRep_apply {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i)) (g : G) (f : ∀ i, V i) (i : ι) :
    piRep V ρ g f i = ρ i g (f i) := rfl

end

end HananyPuder.W2HP.PartD
end

section
/-!
# q288: linear independence of the character polynomials

At one large `N` the characters of the `μ[N]` are the Specht characters of pairwise distinct
partitions, hence orthonormal; a vanishing finite combination of the `q μ` evaluates to a vanishing
combination of those characters.
-/

open StrongConv

namespace HananyPuder.W2Q288.PartL

open OAI.Saxl HananyPuder.W2HP.PartR HananyPuder.W2HP.PartB

noncomputable section

/-- The partition `μ[N]`, with a junk value below the threshold. -/
def sp (μ : YoungDiagram) (N : ℕ) : Nat.Partition N :=
  if h : Thr μ N then stablePart μ N h else Nat.Partition.indiscrete N

lemma sp_eq (μ : YoungDiagram) (N : ℕ) (h : Thr μ N) : sp μ N = stablePart μ N h := dif_pos h

/-- Equal partitions give equivalent Specht representations. -/
def spechtEquivOfEq {N : ℕ} {p p' : Nat.Partition N} (h : p = p') :
    (spechtRep (partitionTableau p)).Equiv (spechtRep (partitionTableau p')) := by
  subst h
  exact Representation.Equiv.refl _

lemma young_equiv_sp (μ : YoungDiagram) (N : ℕ) (h : Thr μ N) :
    Nonempty ((spechtRep (partitionTableau (sp μ N))).Equiv (youngRep N (stableRows μ N))) := by
  obtain ⟨e⟩ := young_equiv_specht μ N h
  exact ⟨(spechtEquivOfEq (sp_eq μ N h)).trans e.symm⟩

lemma char_young (μ : YoungDiagram) (N : ℕ) (h : Thr μ N) :
    (youngRep N (stableRows μ N)).character = schar (sp μ N) := by
  obtain ⟨e⟩ := young_equiv_sp μ N h
  exact (Representation.char_iso e).symm

lemma ip_zero {n : ℕ} (p : Nat.Partition n) : ip (0 : Equiv.Perm (Fin n) → ℂ) p = 0 := by
  simp [ip]

end

/-- Linear independence of the character polynomials: at one large `N` the characters of the `λ[N]`
are orthonormal and pairwise distinct. -/
theorem linIndep_of_trace (q : YoungDiagram → MvPolynomial ℕ ℚ)
    (hq : ∀ (μ : YoungDiagram) (N : ℕ), μ.cells.card + μ.rowLen 0 ≤ N →
      ∀ σ : Equiv.Perm (Fin N),
        LinearMap.trace ℂ (youngSpace N (stableRows μ N)) (youngAct N (stableRows μ N) σ) =
          MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (q μ)) :
    LinearIndependent ℚ q := by
  classical
  rw [linearIndependent_iff']
  intro s g hg μ hμ
  set N := s.sup fun l => l.cells.card + l.rowLen 0 with hN
  have hthr : ∀ l ∈ s, Thr l N := fun l hl =>
    Finset.le_sup (f := fun l => l.cells.card + l.rowLen 0) hl
  have hqs : ∀ l ∈ s, ∀ σ : Equiv.Perm (Fin N),
      schar (sp l N) σ = MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (q l) := by
    intro l hl σ
    rw [← char_young l N (hthr l hl)]
    exact hq l N (hthr l hl) σ
  have hsum : (∑ l ∈ s, ((g l : ℚ) : ℂ) • schar (sp l N)) = 0 := by
    funext σ
    have h1 := congrArg (MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ))) hg
    rw [map_sum, map_zero] at h1
    rw [Finset.sum_apply, Pi.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [map_smul, Pi.smul_apply, hqs l hl σ, Rat.smul_def, smul_eq_mul]
  have h2 := ip_sum_schar s (fun l => ((g l : ℚ) : ℂ)) (fun l => sp l N) (sp μ N)
  rw [hsum, ip_zero] at h2
  have hfil : (s.filter fun l => sp l N = sp μ N) = {μ} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hl, he⟩
      rw [sp_eq l N (hthr l hl), sp_eq μ N (hthr μ hμ)] at he
      exact stablePart_injective _ _ he
    · rintro rfl
      exact ⟨hμ, rfl⟩
  rw [hfil, Finset.sum_singleton] at h2
  exact_mod_cast h2.symm

end HananyPuder.W2Q288.PartL
end

section
/-!
# q288: the dimension count

The polynomials of weighted degree `≤ k` (weight `i + 1` on the variable `i`) form a space with
basis the monomials of weight `≤ k`; these inject into the Young diagrams with at most `k` cells
(the monomial `m` goes to the diagram with `m i` rows of length `i + 1`). A linearly independent
family `q` with `q μ` of weighted degree `≤ |μ|` therefore spans that space for every `k`.
-/



namespace HananyPuder.W2Q288.PartD

open MvPolynomial

noncomputable section

/-- The sorted list of row lengths of the diagram of the monomial `m`. -/
def rowList (m : ℕ →₀ ℕ) : List ℕ := (m.toMultiset.map (· + 1)).sort (· ≥ ·)

lemma rowList_sorted (m : ℕ →₀ ℕ) : (rowList m).SortedGE :=
  (Multiset.pairwise_sort _ _).sortedGE

/-- The Young diagram with `m i` rows of length `i + 1`. -/
def diag (m : ℕ →₀ ℕ) : YoungDiagram := YoungDiagram.ofRowLens (rowList m) (rowList_sorted m)

lemma rowLens_diag (m : ℕ →₀ ℕ) : (diag m).rowLens = rowList m :=
  YoungDiagram.rowLens_ofRowLens_eq_self (fun x hx => by
    rw [rowList, Multiset.mem_sort, Multiset.mem_map] at hx
    obtain ⟨a, _, rfl⟩ := hx
    omega)

/-- The monomial of a diagram: `m i` = number of rows of length `i + 1`. -/
def mono (μ : YoungDiagram) : ℕ →₀ ℕ :=
  Multiset.toFinsupp ((μ.rowLens : Multiset ℕ).map (· - 1))

lemma mono_diag (m : ℕ →₀ ℕ) : mono (diag m) = m := by
  rw [mono, rowLens_diag, rowList, Multiset.sort_eq, Multiset.map_map]
  have h : ((· - 1) ∘ (· + 1) : ℕ → ℕ) = id := by
    funext x
    simp
  rw [h, Multiset.map_id]
  exact Multiset.toFinsupp_eq_iff.mpr rfl

lemma diag_injective : Function.Injective diag := fun a b h => by
  rw [← mono_diag a, ← mono_diag b, h]

lemma card_diag (m : ℕ →₀ ℕ) :
    (diag m).cells.card = Finsupp.weight (fun i : ℕ => i + 1) m := by
  have h1 := OAI.Saxl.card_eq_sum_rowLens (diag m)
  change (diag m).cells.card = _ at h1
  rw [h1, rowLens_diag, rowList, ← Multiset.sum_coe, Multiset.sort_eq, Finsupp.toMultiset_map,
    Finsupp.sum_toMultiset, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul]),
    Finsupp.weight_apply]

lemma le_weight (m : ℕ →₀ ℕ) (i : ℕ) : m i * (i + 1) ≤ Finsupp.weight (fun i : ℕ => i + 1) m := by
  by_cases hi : i ∈ m.support
  · rw [Finsupp.weight_apply, Finsupp.sum]
    exact Finset.single_le_sum (f := fun j => m j • (j + 1)) (fun _ _ => Nat.zero_le _) hi
  · rw [Finsupp.notMem_support_iff.mp hi]
    simp

/-- A box containing every monomial of weight `≤ k`. -/
def box (k : ℕ) : ℕ →₀ ℕ := ∑ i ∈ Finset.range k, Finsupp.single i k

/-- The monomials of weight `≤ k`. -/
def S (k : ℕ) : Finset (ℕ →₀ ℕ) :=
  (Finset.Icc 0 (box k)).filter fun m => Finsupp.weight (fun i : ℕ => i + 1) m ≤ k

lemma mem_S {k : ℕ} {m : ℕ →₀ ℕ} : m ∈ S k ↔ Finsupp.weight (fun i : ℕ => i + 1) m ≤ k := by
  rw [S, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨fun h => h.2, fun h => ⟨⟨by simp, Finsupp.le_def.mpr fun i => ?_⟩, h⟩⟩
  have hw := le_weight m i
  by_cases hmi : m i = 0
  · rw [hmi]
    exact Nat.zero_le _
  · have hik : i < k := by
      have : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr hmi
      nlinarith
    have hmk : m i ≤ k := by nlinarith
    simp only [box, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    simp [Finset.mem_range.mpr hik, hmk]

/-- The polynomials of weighted degree `≤ k`. -/
abbrev V (k : ℕ) : Submodule ℚ (MvPolynomial ℕ ℚ) :=
  restrictSupport ℚ ((S k : Finset (ℕ →₀ ℕ)) : Set (ℕ →₀ ℕ))

lemma mem_V {k : ℕ} {p : MvPolynomial ℕ ℚ}
    (h : weightedTotalDegree (fun i : ℕ => i + 1) p ≤ k) : p ∈ V k := by
  rw [mem_restrictSupport_iff]
  intro d hd
  rw [Finset.mem_coe, mem_S]
  exact (le_weightedTotalDegree _ hd).trans h

instance (k : ℕ) : FiniteDimensional ℚ (V k) :=
  Module.Finite.of_basis (basisRestrictSupport ℚ _)

lemma finrank_V (k : ℕ) : Module.finrank ℚ (V k) = (S k).card := by
  rw [Module.finrank_eq_card_basis (basisRestrictSupport ℚ _)]
  simp

end

/-- The dimension count: a linearly independent family indexed by Young diagrams, with `q μ` of weighted
degree at most `|μ|` (weight `i + 1` on the variable `i`), spans all polynomials. -/
theorem span_eq_top_of_linIndep (q : YoungDiagram → MvPolynomial ℕ ℚ) (hli : LinearIndependent ℚ q)
    (hdeg : ∀ μ : YoungDiagram,
      MvPolynomial.weightedTotalDegree (fun i : ℕ => i + 1) (q μ) ≤ μ.cells.card) :
    Submodule.span ℚ (Set.range q) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro p _
  set k := weightedTotalDegree (fun i : ℕ => i + 1) p with hk
  have hp : p ∈ V k := mem_V le_rfl
  set T := (S k).image diag with hT
  have hTV : ∀ μ ∈ T, q μ ∈ V k := by
    intro μ hμ
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hμ
    exact mem_V ((hdeg _).trans (by rw [card_diag]; exact mem_S.mp hm))
  have hle : Submodule.span ℚ (q '' (T : Set YoungDiagram)) ≤ V k := by
    rw [Submodule.span_le]
    rintro _ ⟨μ, hμ, rfl⟩
    exact hTV μ hμ
  have hli' : LinearIndependent ℚ (fun μ : (T : Set YoungDiagram) => q μ) :=
    hli.comp _ Subtype.val_injective
  have hrank : Module.finrank ℚ (Submodule.span ℚ (q '' (T : Set YoungDiagram))) =
      Module.finrank ℚ (V k) := by
    rw [Set.image_eq_range, finrank_span_eq_card hli', finrank_V, hT]
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
    exact Finset.card_image_of_injective _ diag_injective
  have heq := Submodule.eq_of_le_of_finrank_eq hle hrank
  have hp' : p ∈ Submodule.span ℚ (q '' (T : Set YoungDiagram)) := heq ▸ hp
  exact Submodule.span_mono (Set.image_subset_range _ _) hp'

end HananyPuder.W2Q288.PartD
end

section
open StrongConv

namespace HananyPuder.W2Q288

/-- Hanany–Puder Proposition B.2 in full, from the weighted-degree statement. -/
theorem b2_main :
    ∃ q : YoungDiagram → MvPolynomial ℕ ℚ,
      (∀ (μ : YoungDiagram) (N : ℕ), μ.cells.card + μ.rowLen 0 ≤ N →
        ∀ σ : Equiv.Perm (Fin N),
          LinearMap.trace ℂ (youngSpace N (stableRows μ N)) (youngAct N (stableRows μ N) σ) =
            MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (q μ)) ∧
      LinearIndependent ℚ q ∧ Submodule.span ℚ (Set.range q) = ⊤ := by
  obtain ⟨q, hq, hdeg⟩ := HananyPuder.exists_trace_youngAct_eq_aeval_and_weightedTotalDegree_le
  have hli := PartL.linIndep_of_trace q hq
  exact ⟨q, hq, hli, PartD.span_eq_top_of_linIndep q hli hdeg⟩

end HananyPuder.W2Q288
end

open HananyPuder.W2Q288 in
theorem solution : type_of% @HananyPuder.W2Q288.b2_main := @HananyPuder.W2Q288.b2_main
