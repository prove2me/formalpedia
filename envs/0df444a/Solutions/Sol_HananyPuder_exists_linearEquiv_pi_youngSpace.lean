-- Prove2me | solution 1 for HananyPuder.exists_linearEquiv_pi_youngSpace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T08:39:31.527202+00:00
-- url     : https://prove2.me/submissions/deca2290-609f-4040-bd19-5faa4f11c613

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Theorems.Thm_OAI_Saxl_specht_irreducible
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
import Theorems.Thm_OAI_Saxl_irreducible_equiv_specht
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4
import Theorems.Thm_StrongConv_exists_linearEquiv_youngSpace_specht
import Theorems.Thm_HananyPuder_exists_trace_youngAct_eq_aeval_and_linearIndependent_and_span_eq_top
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
# Decomposition of a finite-dimensional representation of `S_n` into Specht modules

Maschke + `irreducible_equiv_specht`: every finite-dimensional complex representation of `S_n` is
equivalent to a product of Specht modules, and its character is the sum of their characters.
-/

namespace HananyPuder.W2HP.PartD

open OAI.Saxl Representation HananyPuder.W2HP.PartR

noncomputable section

variable {G : Type} [Group G]

lemma eqv_apply {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (g : G) (v : V) :
    e.toLinearEquiv (ρ g v) = σ g (e.toLinearEquiv v) :=
  IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v

/-- The product representation of a family of representations. -/
def piRep {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) : Representation ℂ G (∀ i, V i) where
  toFun g := LinearMap.pi (fun i => ρ i g ∘ₗ LinearMap.proj i)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp] lemma piRep_apply {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i)) (g : G) (f : ∀ i, V i) (i : ι) :
    piRep V ρ g f i = ρ i g (f i) := rfl

/-- Reindexing a product representation along an equivalence of index types. -/
def piRepCongrLeft {ι J : Type} (e : ι ≃ J) (V : J → Type) [∀ j, AddCommGroup (V j)]
    [∀ j, Module ℂ (V j)] (ρ : ∀ j, Representation ℂ G (V j)) :
    (piRep V ρ).Equiv (piRep (fun i => V (e i)) (fun i => ρ (e i))) :=
  Representation.Equiv.mk (LinearEquiv.piCongrLeft ℂ V e).symm (fun g => by
    ext f i
    simp [LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft'])

/-- A product of equivalences. -/
def piRepCongrRight {ι : Type} (V W : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ G (V i)) (σ : ∀ i, Representation ℂ G (W i))
    (e : ∀ i, (ρ i).Equiv (σ i)) : (piRep V ρ).Equiv (piRep W σ) :=
  Representation.Equiv.mk (LinearEquiv.piCongrRight (fun i => (e i).toLinearEquiv)) (fun g => by
    ext f i
    exact eqv_apply (e i) g (f i))

/-- A product of two equivalences. -/
def prodCongr {V₁ V₂ W₁ W₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {σ₁ : Representation ℂ G W₁} {σ₂ : Representation ℂ G W₂}
    (e₁ : ρ₁.Equiv σ₁) (e₂ : ρ₂.Equiv σ₂) : (ρ₁.prod ρ₂).Equiv (σ₁.prod σ₂) :=
  Representation.Equiv.mk (LinearEquiv.prodCongr e₁.toLinearEquiv e₂.toLinearEquiv) (fun g =>
    LinearMap.ext fun x => Prod.ext (eqv_apply e₁ g x.1) (eqv_apply e₂ g x.2))

/-- Splitting off the `none` factor of a product over `Option ι`. -/
def piOptionEquiv {ι : Type} (V : Option ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i)) :
    ((ρ none).prod (piRep (fun i => V (some i)) (fun i => ρ (some i)))).Equiv (piRep V ρ) :=
  Representation.Equiv.mk (LinearEquiv.piOptionEquivProd ℂ).symm (fun g => by
    ext x o
    · cases o <;> rfl
    · cases o <;> rfl)

/-- The direct sum of two complementary subrepresentations. -/
def complEquiv {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (W U : Subrepresentation ρ) (h : IsCompl W.toSubmodule U.toSubmodule) :
    (W.toRepresentation.prod U.toRepresentation).Equiv ρ :=
  Representation.Equiv.mk (Submodule.prodEquivOfIsCompl W.toSubmodule U.toSubmodule h)
    (fun g => by
      ext x
      · simp [Subrepresentation.toRepresentation]
      · simp [Subrepresentation.toRepresentation])

lemma char_prod {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    (ρ.prod σ).character = ρ.character + σ.character := by
  ext g
  exact LinearMap.trace_prodMap' (ρ g) (σ g)

/-- A nonzero subrepresentation of minimal dimension is irreducible. -/
lemma isIrreducible_of_min {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V} (W : Subrepresentation ρ) (hW : W ≠ ⊥)
    (hmin : ∀ X : Subrepresentation ρ, X ≠ ⊥ →
      Module.finrank ℂ W.toSubmodule ≤ Module.finrank ℂ X.toSubmodule) :
    IsIrreducible W.toRepresentation := by
  have hW' : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun X => ?_ }
  · have h1 : (⟨w, hw⟩ : W.toSubmodule) ∈ (⊤ : Subrepresentation W.toRepresentation) :=
      Submodule.mem_top
    rw [← h] at h1
    change (⟨w, hw⟩ : W.toSubmodule) ∈ (⊥ : Submodule ℂ W.toSubmodule) at h1
    rw [Submodule.mem_bot] at h1
    exact hw0 (congrArg Subtype.val h1)
  · let X' : Subrepresentation ρ :=
      { toSubmodule := X.toSubmodule.map W.toSubmodule.subtype
        apply_mem_toSubmodule := by
          intro g v hv
          obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
          exact Submodule.mem_map.mpr ⟨W.toRepresentation g x, X.apply_mem_toSubmodule g hx, rfl⟩ }
    by_cases hX : X = ⊥
    · exact Or.inl hX
    right
    have hX' : X.toSubmodule ≠ ⊥ := fun h => hX (Subrepresentation.toSubmodule_injective h)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX'
    have hX'ne : X' ≠ ⊥ := by
      intro h
      have : (x : V) ∈ X'.toSubmodule := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      rw [h] at this
      change (x : V) ∈ (⊥ : Submodule ℂ V) at this
      rw [Submodule.mem_bot] at this
      exact hx0 (Subtype.ext this)
    have hle : X'.toSubmodule ≤ W.toSubmodule := by
      intro v hv
      obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hv
      exact y.2
    have heq : X'.toSubmodule = W.toSubmodule :=
      Submodule.eq_of_le_of_finrank_le hle (hmin X' hX'ne)
    apply Subrepresentation.toSubmodule_injective
    apply eq_top_iff.mpr
    intro y _
    have : (y : V) ∈ X'.toSubmodule := by rw [heq]; exact y.2
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp this
    have : z = y := Subtype.ext hzy
    exact this ▸ hz

/-- Specht module of a partition. -/
abbrev SP {n : ℕ} (p : Nat.Partition n) := Specht (partitionTableau p)

/-- Every finite-dimensional complex representation of `S_n` is equivalent to a product of
Specht modules, and its character is the sum of their characters. -/
theorem decomp {n : ℕ} :
    ∀ (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (Equiv.Perm (Fin n)) V), Module.finrank ℂ V = d →
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (p : ι → Nat.Partition n),
        Nonempty (ρ.Equiv (piRep (fun i => SP (p i)) (fun i => spechtRep (partitionTableau (p i)))))
        ∧ ρ.character = ∑ i, schar (p i) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ ρ hd
  classical
  by_cases hV : Subsingleton V
  · refine ⟨PEmpty, inferInstance, inferInstance, PEmpty.elim, ⟨?_⟩, ?_⟩
    · exact Representation.Equiv.mk (LinearEquiv.ofSubsingleton _ _)
        (fun g => LinearMap.ext fun x => Subsingleton.elim _ _)
    · ext g
      simp only [Finset.univ_eq_empty, Finset.sum_empty, Pi.zero_apply]
      have : ρ g = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
      simp [Representation.character, this]
  have : NeZero (Nat.card (Equiv.Perm (Fin n)) : ℂ) := ⟨complex_card_ne_zero _⟩
  rw [not_subsingleton_iff_nontrivial] at hV
  -- a nonzero subrepresentation of minimal dimension
  have hS : ∃ X : Subrepresentation ρ, X ≠ ⊥ := by
    refine ⟨⊤, fun h => ?_⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have : v ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [h] at this
    change v ∈ (⊥ : Submodule ℂ V) at this
    exact hv ((Submodule.mem_bot ℂ).mp this)
  let m := Nat.find (p := fun k => ∃ X : Subrepresentation ρ, X ≠ ⊥ ∧
    Module.finrank ℂ X.toSubmodule = k) (by obtain ⟨X, hX⟩ := hS; exact ⟨_, X, hX, rfl⟩)
  obtain ⟨W, hW, hWm⟩ := Nat.find_spec (p := fun k => ∃ X : Subrepresentation ρ, X ≠ ⊥ ∧
    Module.finrank ℂ X.toSubmodule = k) (by obtain ⟨X, hX⟩ := hS; exact ⟨_, X, hX, rfl⟩)
  have hmin : ∀ X : Subrepresentation ρ, X ≠ ⊥ →
      Module.finrank ℂ W.toSubmodule ≤ Module.finrank ℂ X.toSubmodule := by
    intro X hX
    rw [hWm]
    exact Nat.find_min' _ ⟨X, hX, rfl⟩
  have hirr := isIrreducible_of_min W hW hmin
  obtain ⟨U, hU⟩ := exists_isCompl W
  have hc : IsCompl W.toSubmodule U.toSubmodule := by
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hU ⊢
    exact ⟨congrArg Subrepresentation.toSubmodule hU.1,
      congrArg Subrepresentation.toSubmodule hU.2⟩
  have hdim := Submodule.finrank_add_eq_of_isCompl hc
  have hWpos : 0 < Module.finrank ℂ W.toSubmodule := by
    apply Module.finrank_pos_iff.mpr
    have hW' : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
    exact Submodule.nontrivial_iff_ne_bot.mpr hW'
  obtain ⟨ι, _, _, p, ⟨eU⟩, hχU⟩ := ih (Module.finrank ℂ U.toSubmodule) (by omega)
    U.toSubmodule U.toRepresentation rfl
  obtain ⟨p0, ⟨eW⟩⟩ := irreducible_equiv_specht W.toRepresentation
  let q : Option ι → Nat.Partition n := fun o => o.elim p0 p
  refine ⟨Option ι, inferInstance, inferInstance, q, ⟨?_⟩, ?_⟩
  · exact (complEquiv W U hc).symm.trans ((prodCongr eW eU).trans
      (piOptionEquiv (fun i => SP (q i)) (fun i => spechtRep (partitionTableau (q i)))))
  · rw [Fintype.sum_option, ← char_iso (complEquiv W U hc), char_prod, char_iso eW, hχU]
    rfl

end

end HananyPuder.W2HP.PartD
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
/-! Bridge: Hanany–Puder Proposition B.2 (published, over `ℚ`) gives the `ℂ`-form used by the
Blueprint (`charPoly_exists`). -/

open StrongConv

namespace HananyPuder.W2HP.PartQ

theorem charPoly_exists :
    ∃ q : YoungDiagram → MvPolynomial ℕ ℂ,
      (∀ (μ : YoungDiagram) (N : ℕ), μ.cells.card + μ.rowLen 0 ≤ N →
        ∀ σ : Equiv.Perm (Fin N),
          LinearMap.trace ℂ (youngSpace N (stableRows μ N)) (youngAct N (stableRows μ N) σ) =
            MvPolynomial.eval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (q μ)) ∧
      ∀ f : MvPolynomial ℕ ℂ, f ∈ Submodule.span ℂ (Set.range q) := by
  obtain ⟨q, hq, -, hspan⟩ :=
    HananyPuder.exists_trace_youngAct_eq_aeval_and_linearIndependent_and_span_eq_top
  refine ⟨fun μ => MvPolynomial.map (algebraMap ℚ ℂ) (q μ), ?_, ?_⟩
  · intro μ N hN σ
    rw [hq μ N hN σ, MvPolynomial.eval_map, MvPolynomial.aeval_def]
  · intro f
    set S := Submodule.span ℂ (Set.range fun μ => MvPolynomial.map (algebraMap ℚ ℂ) (q μ))
    have hmap : ∀ p ∈ Submodule.span ℚ (Set.range q), MvPolynomial.map (algebraMap ℚ ℂ) p ∈ S := by
      intro p hp
      induction hp using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨μ, rfl⟩ := hx
        exact Submodule.subset_span ⟨μ, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
        exact Submodule.smul_mem _ _ hx
    have hmono : ∀ s : ℕ →₀ ℕ, MvPolynomial.monomial s (1 : ℂ) ∈ S := by
      intro s
      have h1 : MvPolynomial.monomial s (1 : ℚ) ∈ Submodule.span ℚ (Set.range q) := by
        rw [hspan]; exact Submodule.mem_top
      simpa using hmap _ h1
    rw [MvPolynomial.as_sum f]
    refine Submodule.sum_mem _ fun s _ => ?_
    have : MvPolynomial.monomial s (f.coeff s) = f.coeff s • MvPolynomial.monomial s (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (hmono s)

end HananyPuder.W2HP.PartQ
end

section
/-!
# Hanany–Puder Proposition B.2, applied form (blueprint)

Every stable representation is, for `N ≥ N₀` and `N ≥ |μ_j| + (μ_j)₁`, equivalent to
`∏_j λ^{(j)}[N]` for a fixed finite family of Young diagrams.

The one input left as a stub is **Fact C** (`charPoly_exists`): Hanany–Puder Proposition B.2
itself (v4 p. 46: the stable irreducible characters `χ^λ`, `N ≥ |λ| + λ₁`, are given by elements
`q_λ` of `𝒜 = ℚ[ξ₁, ξ₂, …]`, and these elements form a linear basis of `𝒜`; Macdonald,
*Symmetric functions and Hall polynomials*, I.7 Ex. 14). We only use the spanning half of the basis
statement (over `ℂ`, which follows from the `ℚ`-basis statement).

Route: expand `φ = Σ_λ c_λ q_λ`; at one large `N*` the coefficient `c_λ` is the multiplicity
`dim Hom(λ[N*], π_{N*}) ∈ ℕ` (orthonormality of Specht characters, which uses shape rigidity,
`B2PartR`); so `φ = Σ_j q_{μ_j}` as polynomials, with `μ_j` the `λ`'s repeated `c_λ` times. At
any admissible `N`, `Tr π_N = Σ_j χ^{μ_j[N]}`; decomposing `π_N` into Specht modules (`B2PartD`)
and comparing multiplicities gives the equivalence.
-/

open StrongConv OAI.Saxl Representation HananyPuder.W2HP.PartR HananyPuder.W2HP.PartD
  HananyPuder.W2HP.PartB

namespace HananyPuder.W2HP

/-- **Fact C** (Hanany–Puder Proposition B.2; Macdonald I.7 Ex. 14): for every Young diagram `λ`
there is a polynomial `q_λ` in `ξ₁, ξ₂, …` (the variable `i` standing for `ξ_{i+1}`) giving the
character of `λ[N]` for every `N ≥ |λ| + λ₁`, and the `q_λ` span all polynomials. -/
theorem charPoly_exists :
    ∃ q : YoungDiagram → MvPolynomial ℕ ℂ,
      (∀ (μ : YoungDiagram) (N : ℕ), μ.cells.card + μ.rowLen 0 ≤ N →
        ∀ σ : Equiv.Perm (Fin N),
          LinearMap.trace ℂ (youngSpace N (stableRows μ N)) (youngAct N (stableRows μ N) σ) =
            MvPolynomial.eval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (q μ)) ∧
      ∀ f : MvPolynomial ℕ ℂ, f ∈ Submodule.span ℂ (Set.range q) :=
  HananyPuder.W2HP.PartQ.charPoly_exists

noncomputable section

/-- The representation `π_N` on `EuclideanSpace`. -/
def piRepOf (π : StableRep) (N : ℕ) :
    Representation ℂ (Equiv.Perm (Fin N)) (EuclideanSpace ℂ (Fin (π.dim N))) where
  toFun σ := (Matrix.toEuclideanCLM (𝕜 := ℂ)
    (π.π N σ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) : _ →ₗ[ℂ] _)
  map_one' := by simp
  map_mul' σ τ := by simp

lemma piRepOf_character (π : StableRep) (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    (piRepOf π N).character σ = (π.π N σ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace := by
  change LinearMap.trace ℂ _ (Matrix.toEuclideanLin _) = _
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin (π.dim N)) ℂ).toBasis,
    LinearMap.toMatrix_toLin]

/-- The partition `μ[N]`, with a junk value below the threshold. -/
def sp (μ : YoungDiagram) (N : ℕ) : Nat.Partition N :=
  if h : Thr μ N then stablePart μ N h else Nat.Partition.indiscrete N

lemma sp_eq (μ : YoungDiagram) (N : ℕ) (h : Thr μ N) : sp μ N = stablePart μ N h := dif_pos h

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
  exact (char_iso e).symm

lemma ip_eq_finrank {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) (p : Nat.Partition N) :
    ip ρ.character p = (Module.finrank ℂ
      (IntertwiningMap (spechtRep (partitionTableau p)) ρ) : ℂ) := by
  let : Invertible (Nat.card (Equiv.Perm (Fin N)) : ℂ) :=
    invertibleOfNonzero (complex_card_ne_zero _)
  exact card_inv_mul_sum_char_mul_char_eq_finrank (spechtRep (partitionTableau p)) ρ

/-- Hanany–Puder Proposition B.2, applied form. -/
theorem b2_dev (π : StableRep) :
    ∃ (s : ℕ) (μ : Fin s → YoungDiagram), ∀ N : ℕ, π.N₀ ≤ N →
      (∀ j, (μ j).cells.card + (μ j).rowLen 0 ≤ N) →
      ∃ e : EuclideanSpace ℂ (Fin (π.dim N)) ≃ₗ[ℂ]
          ((j : Fin s) → youngSpace N (stableRows (μ j) N)),
        ∀ (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin (π.dim N))),
          e (Matrix.toEuclideanCLM (𝕜 := ℂ)
              (π.π N σ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) x) =
            fun j => youngAct N (stableRows (μ j) N) σ (e x j) := by
  classical
  obtain ⟨q, hq, hspan⟩ := charPoly_exists
  set φ' : MvPolynomial ℕ ℂ := MvPolynomial.rename (fun i : Fin π.r => (i : ℕ)) π.φ with hφ'
  -- the character of `π_N` is `φ'` evaluated at the `ξ`'s
  have hχ : ∀ N, π.N₀ ≤ N → ∀ σ : Equiv.Perm (Fin N), (piRepOf π N).character σ =
      MvPolynomial.eval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) φ' := by
    intro N hN σ
    rw [piRepOf_character, π.trace_eq N hN σ, hφ', MvPolynomial.eval_rename]
    rfl
  -- the character of `λ[N]` is `q λ` evaluated at the `ξ`'s
  have hqs : ∀ (μ : YoungDiagram) (N : ℕ), Thr μ N → ∀ σ : Equiv.Perm (Fin N),
      schar (sp μ N) σ = MvPolynomial.eval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (q μ) := by
    intro μ N h σ
    rw [← char_young μ N h]
    exact hq μ N h σ
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (hspan φ')
  set F := c.support with hF
  have hφc : φ' = ∑ l ∈ F, c l • q l := hc.symm
  -- a large `N*`
  set Nst := max π.N₀ (F.sup fun l => l.cells.card + l.rowLen 0) with hNst
  have hNst0 : π.N₀ ≤ Nst := le_max_left _ _
  have hthrF : ∀ l ∈ F, Thr l Nst := fun l hl =>
    le_trans (Finset.le_sup (f := fun l => l.cells.card + l.rowLen 0) hl) (le_max_right _ _)
  -- the multiplicities at `N*`
  let n : YoungDiagram → ℕ := fun l => Module.finrank ℂ
    (IntertwiningMap (spechtRep (partitionTableau (sp l Nst))) (piRepOf π Nst))
  have hcn : ∀ l ∈ F, c l = (n l : ℂ) := by
    intro l hl
    have hexp : (piRepOf π Nst).character = ∑ l' ∈ F, c l' • schar (sp l' Nst) := by
      ext σ
      rw [hχ Nst hNst0 σ, hφc, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun l' hl' => ?_
      rw [MvPolynomial.smul_eval, Pi.smul_apply, smul_eq_mul, hqs l' Nst (hthrF l' hl') σ,
        mul_comm]
    have h1 := ip_eq_finrank (piRepOf π Nst) (sp l Nst)
    rw [hexp, ip_sum_schar] at h1
    rw [← h1]
    have hfil : (F.filter fun l' => sp l' Nst = sp l Nst) = {l} := by
      ext l'
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hl', he⟩
        rw [sp_eq l' Nst (hthrF l' hl'), sp_eq l Nst (hthrF l hl)] at he
        exact stablePart_injective _ _ he
      · rintro rfl
        exact ⟨hl, rfl⟩
    rw [hfil, Finset.sum_singleton]
  -- the family `μ`: each `λ ∈ F` repeated `n λ` times
  let J := Σ l : F, Fin (n l)
  let eJ := Fintype.equivFin J
  let s := Fintype.card J
  let μ : Fin s → YoungDiagram := fun j => ((eJ.symm j).1 : YoungDiagram)
  have hsumμ : ∀ f : YoungDiagram → ℂ, ∑ j, f (μ j) = ∑ l ∈ F, (n l : ℂ) * f l := by
    intro f
    rw [← Finset.sum_coe_sort F]
    rw [show (∑ j, f (μ j)) = ∑ x : J, f x.1 from
      Equiv.sum_comp eJ.symm (fun x : J => f x.1), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp
  have hφμ : ∀ N (σ : Equiv.Perm (Fin N)),
      MvPolynomial.eval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) φ' =
        ∑ j, MvPolynomial.eval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (q (μ j)) := by
    intro N σ
    rw [hsumμ (fun l => MvPolynomial.eval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (q l)), hφc,
      map_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [MvPolynomial.smul_eval, hcn l hl, mul_comm]
  refine ⟨s, μ, fun N hN hthr => ?_⟩
  -- the character of `π_N` is the sum of the characters of the `μ_j[N]`
  have hχN : (piRepOf π N).character = ∑ j, (1 : ℂ) • schar (sp (μ j) N) := by
    ext σ
    rw [hχ N hN σ, hφμ N σ, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_smul, hqs (μ j) N (hthr j) σ]
  -- decompose `π_N` into Specht modules
  obtain ⟨ι, _, _, p, ⟨eπ⟩, hχp⟩ := decomp _ _ (piRepOf π N) rfl
  have hcount : ∀ r : Nat.Partition N,
      Fintype.card {i // p i = r} = Fintype.card {j // sp (μ j) N = r} := by
    intro r
    have h1 := ip_sum_schar Finset.univ (fun _ => (1 : ℂ)) p r
    have h2 := ip_sum_schar Finset.univ (fun _ => (1 : ℂ)) (fun j => sp (μ j) N) r
    simp only [one_smul] at h1
    rw [← hχp] at h1
    rw [← hχN] at h2
    rw [h1] at h2
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact_mod_cast h2
  let eι : ι ≃ Fin s := Equiv.ofFiberEquiv (fun r => Fintype.equivOfCardEq (hcount r))
  have heι : ∀ i, sp (μ (eι i)) N = p i := fun i =>
    Equiv.ofFiberEquiv_map (fun r => Fintype.equivOfCardEq (hcount r)) i
  -- assemble the equivalence
  let E1 := piRepCongrRight (fun i => SP (p i)) (fun i => SP (sp (μ (eι i)) N))
    (fun i => spechtRep (partitionTableau (p i)))
    (fun i => spechtRep (partitionTableau (sp (μ (eι i)) N)))
    (fun i => spechtEquivOfEq (heι i).symm)
  let E2 := (piRepCongrLeft eι (fun j => SP (sp (μ j) N))
    (fun j => spechtRep (partitionTableau (sp (μ j) N)))).symm
  let E3 := piRepCongrRight (fun j => SP (sp (μ j) N))
    (fun j => youngSpace N (stableRows (μ j) N))
    (fun j => spechtRep (partitionTableau (sp (μ j) N)))
    (fun j => youngRep N (stableRows (μ j) N))
    (fun j => (young_equiv_sp (μ j) N (hthr j)).some)
  let E := ((eπ.trans E1).trans E2).trans E3
  refine ⟨E.toLinearEquiv, fun σ x => ?_⟩
  exact eqv_apply E σ x

end

end HananyPuder.W2HP
end

open StrongConv in
theorem solution (π : StableRep) :
    ∃ (s : ℕ) (μ : Fin s → YoungDiagram), ∀ N : ℕ, π.N₀ ≤ N →
      (∀ j, (μ j).cells.card + (μ j).rowLen 0 ≤ N) →
      ∃ e : EuclideanSpace ℂ (Fin (π.dim N)) ≃ₗ[ℂ]
          ((j : Fin s) → youngSpace N (stableRows (μ j) N)),
        ∀ (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin (π.dim N))),
          e (Matrix.toEuclideanCLM (𝕜 := ℂ)
              (π.π N σ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) x) =
            fun j => youngAct N (stableRows (μ j) N) σ (e x j) :=
  HananyPuder.W2HP.b2_dev π
