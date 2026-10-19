-- Prove2me | solution 1 for OAI.Saxl.saxl_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T12:06:55.776116+00:00
-- url     : https://prove2.me/submissions/2b174bb2-1427-4896-bc5b-1704d0f6b9f6

import Mathlib
import Definitions.Def_Saxl

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

universe uG uV uW uX uAlpha uA uY uZ uR

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

/- Coefficients of position tensors on an alphabet of size `d`. -/

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


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

/- The coefficient of the canonical row word in its polytabloid is one. -/
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


@[simp] theorem mem_staircase {m i j : ℕ} :
    (i, j) ∈ staircase m ↔ i + j < m := by
  change (i, j) ∈ ((Finset.range m) ×ˢ (Finset.range m)).filter
    (fun x => x.1 + x.2 < m) ↔ _
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem staircase_cells_succ (m : ℕ) :
    (staircase (m + 1)).cells = (staircase m).cells ∪ Finset.HasAntidiagonal.antidiagonal m := by
  ext x
  rcases x with ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, mem_staircase, Finset.mem_union,
    Finset.HasAntidiagonal.mem_antidiagonal]
  omega

theorem staircase_card_succ (m : ℕ) :
    (staircase (m + 1)).card = (staircase m).card + (m + 1) := by
  change (staircase (m + 1)).cells.card = _
  rw [staircase_cells_succ, Finset.card_union_of_disjoint]
  · rw [Finset.Nat.card_antidiagonal]
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases x with ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, mem_staircase] at hx
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hy
    omega

@[simp] theorem staircase_card_zero : (staircase 0).card = 0 := by
  simp [staircase, YoungDiagram.card]

theorem staircase_card_double (m : ℕ) :
    (staircase m).card * 2 = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [staircase_card_succ]
    nlinarith

/- The staircase has triangular cardinality. -/
theorem staircase_card (m : ℕ) : (staircase m).card = m * (m + 1) / 2 := by
  rw [← staircase_card_double]
  simp

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

/- A finite set is the unique maximizer of its strictly signed separator.
Used below for the Ferrers equality case in the Specht submodule theorem. -/
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

/- A column-injective rearrangement of the canonical row word has precisely
Ferrers support. This is the equality-of-margins argument, without using
unproved Specht or Young-rule inputs. -/
lemma ferrers_rearrangement {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n))
    (hinj : Function.Injective (fun i => ((t (g i)).val.1, (t i).val.2))) :
    ∀ i, ((t (g i)).val.1, (t i).val.2) ∈ μ := by
  classical
  let f : Fin n → ℕ × ℕ := fun i => ((t (g i)).val.1, (t i).val.2)
  let w : ℕ × ℕ → ℤ := fun c => 2 * (μ.rowLen c.1 : ℤ) - 2 * c.2 - 1
  have ht : Function.Injective (fun i : Fin n => (t i).val) :=
    Subtype.val_injective.comp t.injective
  have himage : Finset.univ.image (fun i : Fin n => (t i).val) = μ.cells := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (t i).property
    · intro hx
      exact ⟨t.symm ⟨x, hx⟩, by simp⟩
  have he : ∑ x ∈ Finset.univ.image f, w x = ∑ x ∈ μ.cells, w x := by
    rw [← himage, Finset.sum_image (fun _ _ _ _ h => hinj h),
      Finset.sum_image (fun _ _ _ _ h => ht h)]
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Equiv.sum_comp g (fun i => (μ.rowLen (t i).val.1 : ℤ))]
  have heq := finset_eq_of_signed_sum (Finset.univ.image f) μ.cells w
    (fun c hc => by
      have h := YoungDiagram.mem_iff_lt_rowLen.mp hc
      dsimp [w]
      omega)
    (fun c hc => by
      have h : μ.rowLen c.1 ≤ c.2 :=
        le_of_not_gt (fun h => hc (YoungDiagram.mem_iff_lt_rowLen.mpr h))
      dsimp [w]
      omega) he
  intro i
  exact (le_of_eq heq) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/- The complex-valued sign character. -/
def signC {n : ℕ} : Equiv.Perm (Fin n) →* ℂ :=
  ((Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)).comp Equiv.Perm.sign

@[simp] lemma signC_def {n : ℕ} (g : Equiv.Perm (Fin n)) :
    signC g = (((Equiv.Perm.sign g) : ℤ) : ℂ) := rfl

@[simp] lemma signC_inv {n : ℕ} (g : Equiv.Perm (Fin n)) : signC g⁻¹ = signC g := by
  simp [signC_def, Equiv.Perm.sign_inv]

@[simp] lemma signC_mul_self {n : ℕ} (g : Equiv.Perm (Fin n)) : signC g * signC g = 1 := by
  calc signC g * signC g = signC (g⁻¹ * g) := by rw [map_mul, signC_inv]
       _ = 1 := by rw [inv_mul_cancel, map_one]

lemma wordRep_single {n d : ℕ} (g : Equiv.Perm (Fin n)) (a : Fin n → Fin d) :
    wordRep n d g (Pi.single a 1) = Pi.single (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) (1 : ℂ) := by
  classical
  ext b
  change (Pi.single a (1 : ℂ) : WordSpace n d) (b ∘ g) = _
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    have hh := congrFun h (g⁻¹ i)
    simpa using hh
  · intro h
    funext i
    have hh := congrFun h (g i)
    simpa using hh

/- Actual column antisymmetrizer on the word-coordinate module. -/
def columnAlt {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Module.End ℂ (WordSpace n d) := by
  classical
  letI := Fintype.ofFinite (columnGroup t)
  exact ∑ g : columnGroup t,
    signC (g : Equiv.Perm (Fin n)) • wordRep n d (g : Equiv.Perm (Fin n))

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

/- Construction of the witnessing column rearrangement. -/
lemma column_rearrangement {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n))
    (hinj : Function.Injective (fun i => ((t (g i)).val.1, (t i).val.2))) :
    ∃ h : columnGroup t, rowWord t ∘ g = rowWord t ∘ (h : Equiv.Perm (Fin n)) := by
  classical
  let f : Fin n → Fin n := fun i =>
    t.symm ⟨((t (g i)).val.1, (t i).val.2), ferrers_rearrangement t g hinj i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hinj
    have hh := congrArg (fun k => (t k).val) hij
    simpa [f] using hh
  let h : Equiv.Perm (Fin n) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have hcol : h ∈ columnGroup t := by
    intro i
    change (t (f i)).val.2 = _
    simp [f]
  refine ⟨⟨h, hcol⟩, ?_⟩
  funext i
  apply Fin.ext
  change (t (g i)).val.1 = (t (f i)).val.1
  simp [f]

lemma columnAlt_collision {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (i j : Fin n) (hij : i ≠ j)
    (hc : (t i).val.2 = (t j).val.2) (ha : a i = a j) :
    columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
  classical
  let h : columnGroup t := ⟨Equiv.swap i j, fun k => Equiv.apply_swap_eq_self (v := fun l => (t l).val.2) hc k⟩
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

lemma columnAlt_column {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    columnAlt t (Pi.single (rowWord t ∘ (h : Equiv.Perm (Fin n))) 1) =
      signC (h : Equiv.Perm (Fin n)) • polytabloid t := by
  classical
  have he : wordRep n (μ.colLen 0) ((h⁻¹ : columnGroup t) : Equiv.Perm (Fin n))
      (Pi.single (rowWord t) 1) =
      Pi.single (rowWord t ∘ (h : Equiv.Perm (Fin n))) 1 := by
    rw [wordRep_single]
    simp only [Subgroup.coe_inv, inv_inv]
  rw [← he, ← Module.End.mul_apply, columnAlt_mul, LinearMap.smul_apply,
    columnAlt_row, Subgroup.coe_inv, signC_inv]

lemma columnAlt_single {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n)) :
    columnAlt t (Pi.single (rowWord t ∘ g) 1) ∈
      Submodule.span ℂ {polytabloid t} := by
  classical
  by_cases hi : Function.Injective (fun i : Fin n => ((t (g i)).val.1, (t i).val.2))
  · obtain ⟨h, hh⟩ := column_rearrangement t g hi
    rw [hh, columnAlt_column]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · simp only [Function.Injective] at hi
    push Not at hi
    obtain ⟨i, j, hc, hij⟩ := hi
    have ha : (rowWord t ∘ g) i = (rowWord t ∘ g) j := by
      apply Fin.ext
      have hh := congrArg Prod.fst hc
      exact hh
    have hcol := congrArg Prod.snd hc
    rw [columnAlt_collision t _ i j hij hcol ha]
    exact Submodule.zero_mem _

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

lemma mem_cyclic {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) : v ∈ cyclic ρ v := by
  change v ∈ Submodule.span ℂ _
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

lemma cyclic_le {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (P : Subrepresentation ρ) :
    cyclic ρ v ≤ P ↔ v ∈ P := by
  constructor
  · intro h
    exact h (mem_cyclic ρ v)
  · intro hv
    change Submodule.span ℂ _ ≤ P.toSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact P.apply_mem_toSubmodule g hv

/- The actual row-tabloid permutation module, embedded in the word space. -/
def tabloidSub {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :=
  cyclic (wordRep n (μ.colLen 0)) (Pi.single (rowWord t) 1)

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

/- The Ferrers shape forces the column antisymmetrizer to have rank one
on the row-tabloid module. -/
lemma columnAlt_tabloid {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ tabloidSub t) :
    columnAlt t x ∈ Submodule.span ℂ {polytabloid t} := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    dsimp only
    rw [wordRep_single]
    exact columnAlt_single t g⁻¹
  | zero => simpa only [map_zero] using (Submodule.zero_mem (Submodule.span ℂ {polytabloid t}))
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using Submodule.smul_mem _ c ih

@[simp] lemma wordRep_star {n d : ℕ} (g : Equiv.Perm (Fin n)) (x : WordSpace n d) :
    star (wordRep n d g x) = wordRep n d g (star x) := rfl

lemma polytabloid_real {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    star (polytabloid t) = polytabloid t := by
  classical
  unfold polytabloid
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [star_smul, wordRep_star]
  simp only [star_intCast]
  congr 2
  ext a
  simp [Pi.single_apply]

lemma cyclic_star {n d : ℕ} (v : WordSpace n d) (hv : star v = v)
    {x : WordSpace n d} (hx : x ∈ cyclic (wordRep n d) v) :
    star x ∈ cyclic (wordRep n d) v := by
  change star x ∈ (cyclic (wordRep n d) v).toSubmodule
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    dsimp only
    rw [wordRep_star, hv]
    exact (cyclic (wordRep n d) v).apply_mem_toSubmodule g (mem_cyclic _ _)
  | zero => simpa only [star_zero] using (Submodule.zero_mem (cyclic (wordRep n d) v).toSubmodule)
  | add x y hx hy ihx ihy =>
    simpa only [star_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    simpa only [star_smul] using Submodule.smul_mem _ (star c) ih

/- On words, precomposition by a position permutation is a bijection. -/
def wordPerm (n d : ℕ) (g : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n → Fin d) where
  toFun a := a ∘ g
  invFun a := a ∘ (g⁻¹ : Equiv.Perm (Fin n))
  left_inv a := by ext i; simp
  right_inv a := by ext i; simp

lemma wordPair_move {n d : ℕ} (g : Equiv.Perm (Fin n)) (x y : WordSpace n d) :
    dotProduct (wordRep n d g x) y = dotProduct x (wordRep n d g⁻¹ y) := by
  have hh := Equiv.sum_comp (wordPerm n d g)
    (fun a => x a * y (a ∘ (g⁻¹ : Equiv.Perm (Fin n))))
  simpa [dotProduct, wordPerm, wordRep, Function.comp_assoc] using hh

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

lemma specht_detect {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ spechtSub t) (hx0 : x ≠ 0) :
    ∃ g : Equiv.Perm (Fin n), dotProduct (wordRep n (μ.colLen 0) g x) (polytabloid t) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hy : ∀ y ∈ (spechtSub t).toSubmodule, dotProduct x y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      have hh := wordPair_move g⁻¹ x (polytabloid t)
      rw [inv_inv] at hh
      exact hh.symm.trans (h g⁻¹)
    | zero => exact dotProduct_zero _
    | add y z hy hz ihy ihz => rw [dotProduct_add, ihy, ihz, add_zero]
    | smul c y hy ih => rw [dotProduct_smul, ih, smul_zero]
  have hs : star x ∈ (spechtSub t).toSubmodule :=
    cyclic_star (polytabloid t) (polytabloid_real t) hx
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact hx0 (dotProduct_self_star_eq_zero.mp (hy (star x) hs))

/- Every nonzero vector in the genuine complex Specht cyclic subspace
again generates that whole subspace. -/
theorem specht_cyclic_of_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ spechtSub t) (hx0 : x ≠ 0) :
    cyclic (wordRep n (μ.colLen 0)) x = spechtSub t := by
  classical
  apply le_antisymm ((cyclic_le _ _ _).mpr hx)
  apply (cyclic_le _ _ _).mpr
  obtain ⟨g, hg⟩ := specht_detect t hx hx0
  have he : wordRep n (μ.colLen 0) g x ∈ spechtSub t :=
    (spechtSub t).apply_mem_toSubmodule g hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (columnAlt_tabloid t (spechtSub_le_tabloidSub t he))
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    apply hg
    rw [← columnAlt_coefficient, ← hc]
    rfl
  have hh := columnAlt_mem t (cyclic (wordRep n (μ.colLen 0)) x)
    ((cyclic (wordRep n (μ.colLen 0)) x).apply_mem_toSubmodule g (mem_cyclic _ _))
  rw [← hc] at hh
  exact (Submodule.smul_mem_iff _ hc0).mp hh

/- Inclusion of a subrepresentation of a subrepresentation into the ambient space. -/
def subrepAmbient {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (U : Subrepresentation ρ)
    (S : Subrepresentation U.toRepresentation) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.map U.toSubmodule.subtype
  apply_mem_toSubmodule g x hx := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨U.toRepresentation g y, S.apply_mem_toSubmodule g hy, rfl⟩

/- The complex polytabloid module is irreducible. -/
theorem specht_irreducible {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.IsIrreducible (spechtRep t) := by
  classical
  have hb : (⊥ : Subrepresentation (spechtRep t)) ≠ ⊤ := by
    intro h
    have hp : (⟨polytabloid t, mem_cyclic _ _⟩ : Specht t) ∈
        (⊥ : Subrepresentation (spechtRep t)).toSubmodule := by
      rw [h]
      trivial
    have he : (⟨polytabloid t, mem_cyclic _ _⟩ : Specht t) = 0 :=
      (Submodule.mem_bot ℂ).mp hp
    exact polytabloid_ne_zero t (congrArg Subtype.val he)
  let : Nontrivial (Subrepresentation (spechtRep t)) := ⟨⟨⊥, ⊤, hb⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hn : S.toSubmodule ≠ ⊥ := by
    intro h
    exact hS (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff S.toSubmodule).mp hn
  have hv : (x : WordSpace n (μ.colLen 0)) ≠ 0 := by
    intro h
    exact hx0 (Subtype.ext h)
  have hl : cyclic (wordRep n (μ.colLen 0)) x.val ≤ subrepAmbient (spechtSub t) S :=
    (cyclic_le _ _ _).mpr ⟨x, hx, rfl⟩
  rw [specht_cyclic_of_ne_zero t x.property hv] at hl
  apply le_antisymm le_top
  intro y hy
  have hm := hl y.property
  obtain ⟨z, hz, he⟩ := hm
  have he' : z = y := Subtype.ext he
  exact he' ▸ hz

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The ordinary bilinear coordinate pairing restricted to any invariant word subspace. -/
def subrepPairMap {n d : ℕ} (S : Subrepresentation (wordRep n d)) :
    Representation.IntertwiningMap S.toRepresentation S.toRepresentation.dual where
  toLinearMap :=
    { toFun := fun x =>
        { toFun := fun y => dotProduct x.val y.val
          map_add' := by intro y z; exact dotProduct_add _ _ _
          map_smul' := by intro a y; exact dotProduct_smul a _ _ }
      map_add' := by intro x y; ext z; exact add_dotProduct _ _ _
      map_smul' := by intro a x; ext z; exact smul_dotProduct a _ _ }
  isIntertwining' g := by
    ext x y
    exact wordPair_move g x.val y.val

lemma subrepPairMap_injective {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) :
    Function.Injective (subrepPairMap S) := by
  classical
  apply (subrepPairMap S).toLinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hh : subrepPairMap S x = 0 := hx
  have hz : dotProduct x.val (star x.val) = 0 :=
    congrArg (fun f : Module.Dual ℂ S.toSubmodule => f ⟨star x.val, hS x.val x.property⟩) hh
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact Subtype.ext (dotProduct_self_star_eq_zero.mp hz)

/- Complex conjugation-stable invariant word subspaces are canonically self-dual
via bilinear evaluation, yielding equivariant projections. -/
def subrepSelfDual {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) :
    Representation.Equiv S.toRepresentation S.toRepresentation.dual :=
  (subrepPairMap S).ofBijective
    ⟨subrepPairMap_injective S hS,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq (K := ℂ) (V := S.toSubmodule)).symm).mp (subrepPairMap_injective S hS)⟩

/- Actual self-duality of every complex Specht representation. -/
def spechtSelfDual {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.Equiv (spechtRep t) (spechtRep t).dual :=
  subrepSelfDual (spechtSub t) (fun _ hx => cyclic_star _ (polytabloid_real t) hx)

/- Restriction of the ambient bilinear coordinate pairing to an invariant subspace. -/
def subrepPairFromAmbient {n d : ℕ} (S : Subrepresentation (wordRep n d)) :
    Representation.IntertwiningMap (wordRep n d) S.toRepresentation.dual where
  toLinearMap :=
    { toFun := fun x =>
        { toFun := fun y => dotProduct x y.val
          map_add' := by intro y z; exact dotProduct_add _ _ _
          map_smul' := by intro a y; exact dotProduct_smul a _ _ }
      map_add' := by intro x y; ext z; exact add_dotProduct _ _ _
      map_smul' := by intro a x; ext z; exact smul_dotProduct a _ _ }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact wordPair_move g x y.val

/- The genuine equivariant orthogonal-coordinate projection. -/
def subrepProject {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) :
    Representation.IntertwiningMap (wordRep n d) S.toRepresentation :=
  (subrepSelfDual S hS).symm.toIntertwiningMap.comp (subrepPairFromAmbient S)

lemma subrepProject_pair {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule)
    (x : WordSpace n d) (y : S.toSubmodule) :
    dotProduct (subrepProject S hS x).val y.val = dotProduct x y.val := by
  have hh := (subrepSelfDual S hS).apply_symm_apply (subrepPairFromAmbient S x)
  exact congrArg (fun f : Module.Dual ℂ S.toSubmodule => f y) hh

/- A tensor power of a single letter-linear map, in ordinary word coordinates. -/
def wordMap {n d e : ℕ} (L : Fin d → Fin e → ℂ) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n e) where
  toLinearMap :=
    { toFun := fun x b => ∑ a, x a * ∏ i, L (a i) (b i)
      map_add' := by
        intro x y
        ext b
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext b
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
          RingHom.id_apply] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext b
    change (∑ a, x (a ∘ g) * ∏ i, L (a i) (b i)) =
      ∑ a, x a * ∏ i, L (a i) (b (g i))
    apply Eq.trans ?_ (Equiv.sum_comp (wordPerm n d g)
      (fun a => x a * ∏ i, L (a i) (b (g i))))
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [wordPerm]
    congr 1
    exact (Equiv.prod_comp g (fun i => L (a i) (b i))).symm

@[simp] lemma wordMap_single {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (a : Fin n → Fin d) (b : Fin n → Fin e) :
    wordMap L (Pi.single a 1) b = ∏ i, L (a i) (b i) := by
  classical
  simp [wordMap, Pi.single_apply]

/- A nonzero contraction with a real cyclic vector gives an actual nonzero
intertwiner into its cyclic representation. -/
theorem hom_to_cyclic_of_pair {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (S : Subrepresentation (wordRep n d)) (x : S.toSubmodule)
    (u : WordSpace n e) (hu : star u = u)
    (h : dotProduct (wordMap L x.val) u ≠ 0) :
    ∃ f : Representation.IntertwiningMap S.toRepresentation
      (cyclic (wordRep n e) u).toRepresentation, f ≠ 0 := by
  let inc : Representation.IntertwiningMap S.toRepresentation (wordRep n d) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun g => rfl }
  let f := (subrepProject (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx)).comp ((wordMap L).comp inc)
  refine ⟨f, ?_⟩
  intro hf
  have hp := subrepProject_pair (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx) (wordMap L x.val) ⟨u, mem_cyclic _ _⟩
  have he : f x = 0 := by rw [hf]; rfl
  change (subrepProject (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx)) (wordMap L x.val) = 0 at he
  rw [he] at hp
  exact h (hp.symm.trans (zero_dotProduct _))

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A change of tableau enumeration only applies a position permutation. -/
def tableauMove {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) : Equiv.Perm (Fin n) :=
  s.trans t.symm

@[simp] lemma tableauMove_apply {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) (i : Fin n) :
    t (tableauMove s t i) = s i := by simp [tableauMove]

@[simp] lemma tableauMove_inv_apply {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) (i : Fin n) :
    s ((tableauMove s t)⁻¹ i) = t i := by simp [tableauMove, Equiv.Perm.inv_def]

def columnMove {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    columnGroup s ≃ columnGroup t where
  toFun h := ⟨tableauMove s t * h.val * (tableauMove s t)⁻¹, by
    intro i
    simp only [Equiv.Perm.mul_apply, tableauMove_apply]
    rw [h.property, tableauMove_inv_apply]⟩
  invFun h := ⟨(tableauMove s t)⁻¹ * h.val * tableauMove s t, by
    intro i
    simp only [Equiv.Perm.mul_apply, tableauMove_inv_apply]
    rw [h.property, tableauMove_apply]⟩
  left_inv h := by apply Subtype.ext; simp [mul_assoc]
  right_inv h := by apply Subtype.ext; simp [mul_assoc]

lemma rowWord_move {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    rowWord t = rowWord s ∘ ((tableauMove s t)⁻¹ : Equiv.Perm (Fin n)) := by
  funext i
  apply Fin.ext
  exact congrArg (fun c : μ.cells => c.val.1) (tableauMove_inv_apply s t i).symm

lemma polytabloid_move {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    polytabloid t = wordRep n (μ.colLen 0) (tableauMove s t) (polytabloid s) := by
  classical
  let := Fintype.ofFinite (columnGroup s)
  let := Fintype.ofFinite (columnGroup t)
  unfold polytabloid
  rw [map_sum]
  refine (Fintype.sum_equiv (columnMove s t).symm _ _ ?_)
  intro h
  let g := tableauMove s t
  change signC (h : Equiv.Perm (Fin n)) • wordRep n (μ.colLen 0) h.val (Pi.single (rowWord t) 1) =
    wordRep n (μ.colLen 0) g
      (signC ((columnMove s t).symm h).val •
        wordRep n (μ.colLen 0) ((columnMove s t).symm h).val (Pi.single (rowWord s) 1))
  have hs : signC ((columnMove s t).symm h).val = signC h.val := by
    change signC (g⁻¹ * h.val * g) = signC h.val
    rw [map_mul, map_mul, signC_inv]
    calc signC g * signC h.val * signC g = signC h.val * (signC g * signC g) := by ring
         _ = signC h.val := by rw [signC_mul_self, mul_one]
  rw [map_smul, hs]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul]
  change wordRep n (μ.colLen 0) h.val (Pi.single (rowWord t) 1) =
    wordRep n (μ.colLen 0) (g * (g⁻¹ * h.val * g)) (Pi.single (rowWord s) 1)
  have he : g * (g⁻¹ * h.val * g) = h.val * g := by group
  have hv : wordRep n (μ.colLen 0) g (Pi.single (rowWord s) 1) = Pi.single (rowWord t) 1 := by
    rw [wordRep_single, rowWord_move s t]
  rw [he, map_mul, Module.End.mul_apply, hv]

lemma polytabloid_mem_all {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    polytabloid t ∈ spechtSub s := by
  rw [polytabloid_move s t]
  exact (spechtSub s).apply_mem_toSubmodule _ (mem_cyclic _ _)

lemma spechtSub_tableau_independent {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    spechtSub s = spechtSub t := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr (polytabloid_mem_all t s)
  · exact (cyclic_le _ _ _).mpr (polytabloid_mem_all s t)
end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
def splitLeft {n d e : ℕ} (w : Fin n → Fin (d*e)) : Fin n → Fin d :=
  fun i => (finProdFinEquiv.symm (w i)).1

def splitRight {n d e : ℕ} (w : Fin n → Fin (d*e)) : Fin n → Fin e :=
  fun i => (finProdFinEquiv.symm (w i)).2

def mergeWords {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) : Fin n → Fin (d*e) :=
  fun i => finProdFinEquiv (a i, b i)

@[simp] lemma splitLeft_merge {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    splitLeft (mergeWords a b) = a := by ext i; simp [splitLeft, mergeWords]
@[simp] lemma splitRight_merge {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    splitRight (mergeWords a b) = b := by ext i; simp [splitRight, mergeWords]
@[simp] lemma merge_split {n d e : ℕ} (w : Fin n → Fin (d*e)) :
    mergeWords (splitLeft w) (splitRight w) = w := by
  funext i
  exact finProdFinEquiv.apply_symm_apply (w i)

def wordUncurry (n d e : ℕ) :
    ((Fin n → Fin e) → WordSpace n d) ≃ₗ[ℂ] WordSpace n (d*e) where
  toFun f w := f (splitRight w) (splitLeft w)
  invFun z b a := z (mergeWords a b)
  left_inv f := by ext b a; simp
  right_inv z := by ext w; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- Tensor regrouping by positions. -/
def wordTensor (n d e : ℕ) :
    WordSpace n d ⊗[ℂ] WordSpace n e ≃ₗ[ℂ] WordSpace n (d*e) :=
  TensorProduct.piScalarRight ℂ ℂ (WordSpace n d) (Fin n → Fin e) ≪≫ₗ wordUncurry n d e

@[simp] lemma wordTensor_tmul {n d e : ℕ} (x : WordSpace n d) (y : WordSpace n e)
    (w : Fin n → Fin (d*e)) :
    wordTensor n d e (x ⊗ₜ[ℂ] y) w = x (splitLeft w) * y (splitRight w) := by
  change y (splitRight w) • x (splitLeft w) = _
  exact mul_comm _ _

lemma wordTensor_equivariant {n d e : ℕ} (g : Equiv.Perm (Fin n))
    (z : WordSpace n d ⊗[ℂ] WordSpace n e) :
    wordTensor n d e (((wordRep n d).tprod (wordRep n e)) g z) =
      wordRep n (d*e) g (wordTensor n d e z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    ext w
    change wordTensor n d e (wordRep n d g x ⊗ₜ[ℂ] wordRep n e g y) w = _
    change wordTensor n d e (wordRep n d g x ⊗ₜ[ℂ] wordRep n e g y) w =
      wordTensor n d e (x ⊗ₜ[ℂ] y) (w ∘ g)
    simp only [wordTensor_tmul]
    rfl

def wordTensorIntertwiner (n d e : ℕ) :
    Representation.IntertwiningMap ((wordRep n d).tprod (wordRep n e)) (wordRep n (d*e)) where
  toLinearMap := (wordTensor n d e).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    exact wordTensor_equivariant g z

end Saxl

namespace Saxl

/- Transposition is an honest permutation of the self-conjugate staircase. -/
def staircaseSwap (m : ℕ) : (staircase m).cells ≃ (staircase m).cells where
  toFun x := ⟨(x.val.2, x.val.1), by
    have h : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩
  invFun x := ⟨(x.val.2, x.val.1), by
    have h : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev stairTableau (m : ℕ) : Tableau (staircase m).card (staircase m) :=
  canonicalTableau (staircase m) rfl

def stairRowTableau (m : ℕ) : Tableau (staircase m).card (staircase m) :=
  (stairTableau m).trans (staircaseSwap m)

def staircaseWord (m : ℕ) : WordSpace (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0) :=
  wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairTableau m))

def staircaseCyclic (m : ℕ) : Subrepresentation
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)) :=
  cyclic (wordRep _ _) (staircaseWord m)

def spechtInclusion {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.IntertwiningMap (spechtRep t) (wordRep n (μ.colLen 0)) where
  toLinearMap := (spechtSub t).toSubmodule.subtype
  isIntertwining' _ := rfl

def staircaseTensorMap (m : ℕ) :
    Representation.IntertwiningMap ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m)))
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)) :=
  (wordTensorIntertwiner _ _ _).comp
    ((spechtInclusion (stairTableau m)).tensor (spechtInclusion (stairTableau m)))

lemma staircaseTensorMap_injective (m : ℕ) : Function.Injective (staircaseTensorMap m) := by
  apply (wordTensor _ _ _).injective.comp
  exact TensorProduct.map_injective_of_flat_flat _ _
    (spechtSub (stairTableau m)).toSubmodule.subtype_injective
    (spechtSub (stairTableau m)).toSubmodule.subtype_injective

lemma staircaseCyclic_le_tensorRange (m : ℕ) :
    staircaseCyclic m ≤ (staircaseTensorMap m).range := by
  apply (cyclic_le _ _ _).mpr
  refine ⟨(⟨polytabloid (stairRowTableau m), polytabloid_mem_all _ _⟩ : Specht (stairTableau m)) ⊗ₜ[ℂ]
    (⟨polytabloid (stairTableau m), mem_cyclic _ _⟩ : Specht (stairTableau m)), ?_⟩
  rfl

attribute [irreducible] staircaseTensorMap

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/
def highRowEquiv (h s : ℕ) :
    {x : (staircase (h+s)).cells // s ≤ x.val.2} ≃ (staircase h).cells where
  toFun x := ⟨(x.val.val.1, x.val.val.2 - s), by
    have hx : x.val.val.1 + x.val.val.2 < h+s := mem_staircase.mp x.val.property
    exact mem_staircase.mpr (by have := x.property; omega)⟩
  invFun x := ⟨⟨(x.val.1, x.val.2+s), by
    have hx : x.val.1 + x.val.2 < h := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩, by dsimp; omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    have := x.property
    ext <;> omega
  right_inv x := by apply Subtype.ext; simp

def highColEquiv (h s : ℕ) :
    {x : (staircase (h+s)).cells // s ≤ x.val.1} ≃ (staircase h).cells where
  toFun x := ⟨(x.val.val.1 - s, x.val.val.2), by
    have hx : x.val.val.1 + x.val.val.2 < h+s := mem_staircase.mp x.val.property
    exact mem_staircase.mpr (by have := x.property; omega)⟩
  invFun x := ⟨⟨(x.val.1+s, x.val.2), by
    have hx : x.val.1 + x.val.2 < h := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩, by dsimp; omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    have := x.property
    ext <;> omega
  right_inv x := by apply Subtype.ext; simp

theorem high_positions_rigidity (h s : ℕ)
    (g k : Equiv.Perm (staircase (h+s)).cells)
    (hg : ∀ x, (g x).val.1 = x.val.1)
    (hk : ∀ x, (k x).val.2 = x.val.2)
    (hc : ∀ x, s ≤ (g x).val.2 ↔ s ≤ (k x).val.1) :
    ∀ x, s ≤ (g x).val.2 ↔ x.val.1 + x.val.2 < h := by
  classical
  let A : Finset (staircase (h+s)).cells := Finset.univ.filter (fun x => s ≤ (g x).val.2)
  let B : Finset (staircase (h+s)).cells := Finset.univ.filter (fun x => x.val.1 + x.val.2 < h)
  let eR : A ≃ (staircase h).cells :=
    (Equiv.subtypeEquiv g (by intro x; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and])).trans
      (highRowEquiv h s)
  let eC : A ≃ (staircase h).cells :=
    (Equiv.subtypeEquiv k (by intro x; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; exact hc x)).trans
      (highColEquiv h s)
  let eB : B ≃ (staircase h).cells :=
    { toFun := fun x => ⟨x.val.val, mem_staircase.mpr (by simpa [B] using x.property)⟩
      invFun := fun x => ⟨⟨x.val, mem_staircase.mpr (by
        have hx := mem_staircase.mp x.property; omega)⟩, by simp [B, mem_staircase.mp x.property]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : A.card = B.card := by
    have he := Fintype.card_congr (eR.trans eB.symm)
    simpa using he
  have hrow : ∑ x ∈ A, (x.val.1 : ℤ) = ∑ x ∈ B, (x.val.1 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hR := Equiv.sum_comp eR (fun x => (x.val.1 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.1 : ℤ))
    simpa [eR, eB, highRowEquiv, hg] using hR.trans hB.symm
  have hcol : ∑ x ∈ A, (x.val.2 : ℤ) = ∑ x ∈ B, (x.val.2 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hC := Equiv.sum_comp eC (fun x => (x.val.2 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.2 : ℤ))
    simpa [eC, eB, highColEquiv, hk] using hC.trans hB.symm
  let w := fun x : (staircase (h+s)).cells =>
    2 * (h : ℤ) - 1 - 2 * (x.val.1 : ℤ) - 2 * (x.val.2 : ℤ)
  have he : ∑ x ∈ A, w x = ∑ x ∈ B, w x := by
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [hcard, hrow, hcol]
  have hab := finset_eq_of_signed_sum A B w
    (fun x hx => by
      have hh : x.val.1 + x.val.2 < h := by simpa [B] using hx
      dsimp [w]
      omega)
    (fun x hx => by
      have hh : ¬x.val.1 + x.val.2 < h := by simpa [B] using hx
      dsimp [w]
      omega) he
  intro x
  have := Finset.ext_iff.mp hab x
  simpa [A, B] using this


lemma polytabloid_support {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) (ha : polytabloid t a ≠ 0) :
    ∃ g : columnGroup t, a = rowWord t ∘ (g : Equiv.Perm (Fin n)) := by
  classical
  have hex : ∃ g : columnGroup t, a ∘ (g : Equiv.Perm (Fin n)) = rowWord t := by
    by_contra! hh
    apply ha
    unfold polytabloid
    simp only [Finset.sum_apply, Pi.smul_apply, wordRep, MonoidHom.coe_mk,
      OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
    simp [hh]
  obtain ⟨g, hg⟩ := hex
  refine ⟨g⁻¹, ?_⟩
  funext i
  have he := congrFun hg ((g : Equiv.Perm (Fin n))⁻¹ i)
  simpa using he

/- Local same-high projection in the ordinary pair-letter coordinate space. -/
def sameHighProjection (n d e s : ℕ) :
    Representation.IntertwiningMap (wordRep n (d*e)) (wordRep n (d*e)) where
  toFun z w := if (∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val) then z w else 0
  map_add' z y := by ext w; dsimp; split_ifs <;> simp
  map_smul' c z := by ext w; dsimp; split_ifs <;> simp
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    funext w
    change (if (∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val) then z (w ∘ g) else 0) =
      (if (∀ i, s ≤ (splitLeft (w ∘ g) i).val ↔ s ≤ (splitRight (w ∘ g) i).val) then z (w ∘ g) else 0)
    congr 1
    apply propext
    exact (g.forall_congr_right).symm

theorem staircase_projected_high_positions (h s : ℕ)
    (w : Fin (staircase (h+s)).card → Fin ((staircase (h+s)).colLen 0 * (staircase (h+s)).colLen 0))
    (hw : sameHighProjection _ _ _ s (staircaseWord (h+s)) w ≠ 0) :
    ∀ i, s ≤ (splitLeft w i).val ↔
      ((stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h) := by
  classical
  have heq : ∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val := by
    by_contra hh
    apply hw
    simp [sameHighProjection, hh]
  have hww : staircaseWord (h+s) w ≠ 0 := by
    simpa [sameHighProjection, heq] using hw
  have hp : polytabloid (stairRowTableau (h+s)) (splitLeft w) *
      polytabloid (stairTableau (h+s)) (splitRight w) ≠ 0 := by
    simpa only [staircaseWord, wordTensor_tmul] using hww
  obtain ⟨g, hg⟩ := polytabloid_support (stairRowTableau (h+s)) _ (mul_ne_zero_iff.mp hp).1
  obtain ⟨k, hk⟩ := polytabloid_support (stairTableau (h+s)) _ (mul_ne_zero_iff.mp hp).2
  let t := stairTableau (h+s)
  let gc : Equiv.Perm (staircase (h+s)).cells := (t.symm.trans (g : Equiv.Perm _)).trans t
  let kc : Equiv.Perm (staircase (h+s)).cells := (t.symm.trans (k : Equiv.Perm _)).trans t
  have hgc : ∀ x, (gc x).val.1 = x.val.1 := by
    intro x
    have hh := g.property (t.symm x)
    change (t ((g : Equiv.Perm _) (t.symm x))).val.1 = (t (t.symm x)).val.1 at hh
    simpa [gc] using hh
  have hkc : ∀ x, (kc x).val.2 = x.val.2 := by
    intro x
    have hh := k.property (t.symm x)
    change (t ((k : Equiv.Perm _) (t.symm x))).val.2 = (t (t.symm x)).val.2 at hh
    simpa [kc] using hh
  have hcommon : ∀ x, s ≤ (gc x).val.2 ↔ s ≤ (kc x).val.1 := by
    intro x
    have hh := heq (t.symm x)
    rw [hg, hk] at hh
    exact hh
  have hr := high_positions_rigidity h s gc kc hgc hkc hcommon
  intro i
  have hh := hr (t i)
  rw [hg]
  simpa [gc, t, rowWord, stairRowTableau, staircaseSwap] using hh


lemma columnAlt_left {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    wordRep n d (h : Equiv.Perm (Fin n)) * columnAlt (d := d) t =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC (h : Equiv.Perm (Fin n)) •
    signC ((h * g : columnGroup t) : Equiv.Perm (Fin n)) •
      wordRep n d ((h * g : columnGroup t) : Equiv.Perm (Fin n)) = _
  simp only [Subgroup.coe_mul, map_mul, smul_smul]
  rw [← mul_assoc, signC_mul_self, one_mul]

lemma polytabloid_alternating {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) : wordRep n (μ.colLen 0) (h : Equiv.Perm (Fin n))
      (polytabloid t) = signC (h : Equiv.Perm (Fin n)) • polytabloid t := by
  rw [← columnAlt_row]
  exact congrArg (fun L : Module.End ℂ (WordSpace n (μ.colLen 0)) =>
    L (Pi.single (rowWord t) 1)) (columnAlt_left t h)

/- Move low row letters to the band and high row letters to B_h. -/
def rotateRowCell (h s : ℕ) (x : (staircase (h+s)).cells) : (staircase (h+s)).cells :=
  ⟨(x.val.1, if x.val.2 < h - x.val.1 then x.val.2+s else x.val.2-(h-x.val.1)), by
    have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
    apply mem_staircase.mpr
    split_ifs <;> omega⟩

lemma rotateRowCell_injective (h s : ℕ) : Function.Injective (rotateRowCell h s) := by
  intro x y he
  have hi0 := congrArg (fun z : (staircase (h+s)).cells => z.val.1) he
  have hi : x.val.1 = y.val.1 := hi0
  have hj := congrArg (fun z : (staircase (h+s)).cells => z.val.2) he
  have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
  have hy : y.val.1 + y.val.2 < h+s := mem_staircase.mp y.property
  dsimp [rotateRowCell] at hj
  apply Subtype.ext
  apply Prod.ext hi
  split_ifs at hj <;> omega

def rotateRow (h s : ℕ) : Equiv.Perm (staircase (h+s)).cells :=
  Equiv.ofBijective (rotateRowCell h s) (⟨rotateRowCell_injective h s, Finite.surjective_of_injective (rotateRowCell_injective h s)⟩)

lemma rotateRow_high (h s : ℕ) (x : (staircase (h+s)).cells) :
    s ≤ (rotateRow h s x).val.2 ↔ x.val.1 + x.val.2 < h := by
  have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
  change s ≤ (if x.val.2 < h - x.val.1 then x.val.2+s else x.val.2-(h-x.val.1)) ↔ _
  split_ifs <;> omega

def rotateColumn (h s : ℕ) : Equiv.Perm (staircase (h+s)).cells :=
  ((staircaseSwap (h+s)).trans (rotateRow h s)).trans (staircaseSwap (h+s))

lemma rotateColumn_high (h s : ℕ) (x : (staircase (h+s)).cells) :
    s ≤ (rotateColumn h s x).val.1 ↔ x.val.1 + x.val.2 < h := by
  have hh := rotateRow_high h s (staircaseSwap (h+s) x)
  change s ≤ (rotateRow h s (staircaseSwap (h+s) x)).val.2 ↔ _
  simpa [staircaseSwap, Nat.add_comm] using hh

def rotateRowPositions (h s : ℕ) : columnGroup (stairRowTableau (h+s)) :=
  ⟨((stairTableau (h+s)).trans (rotateRow h s)).trans (stairTableau (h+s)).symm, by
    intro i
    change (stairTableau (h+s) ((stairTableau (h+s)).symm (rotateRow h s (stairTableau (h+s) i)))).val.1 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

def rotateColumnPositions (h s : ℕ) : columnGroup (stairTableau (h+s)) :=
  ⟨((stairTableau (h+s)).trans (rotateColumn h s)).trans (stairTableau (h+s)).symm, by
    intro i
    change (stairTableau (h+s) ((stairTableau (h+s)).symm (rotateColumn h s (stairTableau (h+s) i)))).val.2 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

lemma polytabloid_column_coeff {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : columnGroup t) :
    polytabloid t (rowWord t ∘ (g : Equiv.Perm (Fin n))) = signC (g : Equiv.Perm (Fin n)) := by
  have hh := congrFun (polytabloid_alternating t g) (rowWord t)
  change polytabloid t (rowWord t ∘ (g : Equiv.Perm (Fin n))) =
    signC (g : Equiv.Perm (Fin n)) * polytabloid t (rowWord t) at hh
  simpa [polytabloid_rowWord] using hh

/- The projected generator is genuinely nonzero for every band width,
without assuming a tensor factorization. -/
theorem staircase_projected_ne_zero (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) ≠ 0 := by
  classical
  let a := rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _)
  let b := rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _)
  let w := mergeWords a b
  have ha (i) : s ≤ (a i).val ↔ (stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h := by
    have hh := rotateRow_high h s (stairTableau (h+s) i)
    simpa [a, rowWord, stairRowTableau, rotateRowPositions, staircaseSwap] using hh
  have hb (i) : s ≤ (b i).val ↔ (stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h := by
    have hh := rotateColumn_high h s (stairTableau (h+s) i)
    simpa [b, rowWord, rotateColumnPositions] using hh
  have hp : ∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val := by
    intro i
    simp only [w, splitLeft_merge, splitRight_merge]
    exact (ha i).trans (hb i).symm
  intro hz
  have he := congrFun hz w
  change sameHighProjection _ _ _ s (staircaseWord (h+s)) w = 0 at he
  simp only [sameHighProjection, Representation.IntertwiningMap.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, staircaseWord, wordTensor_tmul, w, splitLeft_merge, splitRight_merge,
    a, b, polytabloid_column_coeff] at he
  have hn (g : Equiv.Perm (Fin (staircase (h+s)).card)) : signC g ≠ 0 := by
    intro hz
    have hh := signC_mul_self g
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have hpab : ∀ i, s ≤ (a i).val ↔ s ≤ (b i).val := fun i => (ha i).trans (hb i).symm
  rw [ite_eq_left hpab] at he
  exact mul_ne_zero (hn _) (hn _) he

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/
def coordinateProjection {n d : ℕ} (P : (Fin n → Fin d) → Prop) :
    Module.End ℂ (WordSpace n d) := by
  classical
  exact {
    toFun := fun x a => if P a then x a else 0
    map_add' := by intros; funext a; by_cases h : P a <;> simp [h]
    map_smul' := by intros; funext a; by_cases h : P a <;> simp [h] }

@[simp] lemma coordinateProjection_apply {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (x : WordSpace n d) (a : Fin n → Fin d) [Decidable (P a)] :
    coordinateProjection P x a = if P a then x a else 0 := by
  classical
  by_cases h : P a <;> simp [coordinateProjection, h]

lemma coordinateProjection_single {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (a : Fin n → Fin d) [Decidable (P a)] :
    coordinateProjection P (Pi.single a 1) = if P a then Pi.single a 1 else 0 := by
  classical
  ext b
  by_cases he : b = a
  · subst b; by_cases h : P a <;> simp [h]
  · by_cases h : P a <;> simp [he, h]

/- Permutations preserving a position sector. -/
def sectorGroup {n : ℕ} (D : Fin n → Prop) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ i, D (g i) ↔ D i}
  one_mem' _ := Iff.rfl
  mul_mem' hg hh i := (hg _).trans (hh i)
  inv_mem' := by
    intro g hg i
    simpa using (hg (g⁻¹ i)).symm

/- The genuine unnormalized signed block alternation. -/
def altWord {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n → Fin d) :
    WordSpace n d := by
  classical
  letI := Fintype.ofFinite G
  exact ∑ g : G, signC (g : Equiv.Perm (Fin n)) •
    wordRep n d (g : Equiv.Perm (Fin n)) (Pi.single a 1)

lemma altWord_move {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (r : G) :
    altWord G (a ∘ (r : Equiv.Perm (Fin n))) =
      signC (r : Equiv.Perm (Fin n)) • altWord G a := by
  classical
  let := Fintype.ofFinite G
  have he : Pi.single (a ∘ (r : Equiv.Perm (Fin n))) (1 : ℂ) =
      wordRep n d (r⁻¹ : G) (Pi.single a 1) := by
    rw [wordRep_single]
    rfl
  unfold altWord
  rw [he]
  simp only [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, Finset.smul_sum]
  apply (Equiv.sum_comp (Equiv.mulRight r) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC ((g*r : G) : Equiv.Perm (Fin n)) •
    wordRep n d (((g*r : G) : Equiv.Perm (Fin n)) * (r : Equiv.Perm (Fin n))⁻¹) (Pi.single a 1) = _
  simp only [Subgroup.coe_mul, map_mul, mul_inv_cancel_right, smul_smul]
  rw [mul_comm (signC (g : Equiv.Perm (Fin n)))]

/- Keeping a prescribed coloring restricts the alternating group to its
sector stabilizer. This is the finite coset calculation behind block-factorization. -/
theorem altWord_sector {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (Q : Fin d → Prop) (D : Fin n → Prop)
    (ha : ∀ i, Q (a i) ↔ D i) :
    coordinateProjection (fun b => ∀ i, Q (b i) ↔ D i) (altWord G a) =
      altWord (G ⊓ sectorGroup D) a := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite ↥(G ⊓ sectorGroup D)
  have hh (g : G) :
      (∀ i, Q ((a ∘ ((g : Equiv.Perm (Fin n))⁻¹ : Equiv.Perm (Fin n))) i) ↔ D i) ↔
        (g : Equiv.Perm (Fin n)) ∈ sectorGroup D := by
    constructor
    · intro h i
      have h' := (ha _).symm.trans (h ((g : Equiv.Perm (Fin n)) i))
      simpa using h'.symm
    · intro h i
      exact (ha _).trans (by simpa using (h (((g : Equiv.Perm (Fin n))⁻¹) i)).symm)
  unfold altWord
  simp only [map_sum, map_smul, wordRep_single, coordinateProjection_single, hh, smul_ite, smul_zero]
  let e : {g : G // (g : Equiv.Perm (Fin n)) ∈ sectorGroup D} ≃ ↥(G ⊓ sectorGroup D) := {
    toFun := fun g => ⟨g.val.val, g.val.property, g.property⟩
    invFun := fun g => ⟨⟨g.val, g.property.1⟩, g.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← Finset.sum_filter]
  rw [← Finset.sum_attach]
  apply Fintype.sum_equiv ?_ _ _ ?_
  · exact (Equiv.subtypeEquivRight (fun g => by simp)).trans e
  · intro g
    rfl

end Saxl

namespace Saxl
/- The prescribed high sector in the actual staircase enumeration. -/
def stairHigh (h s : ℕ) (i : Fin (staircase (h+s)).card) : Prop :=
  (stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h

lemma staircase_projected_sector (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) =
    coordinateProjection (fun w => (∀ i, s ≤ (splitLeft w i).val ↔ stairHigh h s i) ∧
      (∀ i, s ≤ (splitRight w i).val ↔ stairHigh h s i)) (staircaseWord (h+s)) := by
  classical
  ext w
  by_cases he : ∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val
  · by_cases hw : sameHighProjection _ _ _ s (staircaseWord (h+s)) w = 0
    · have hw' : staircaseWord (h+s) w = 0 := by simpa [sameHighProjection, he] using hw
      simp [hw, hw']
    · have hD := staircase_projected_high_positions h s w hw
      have hD' : ∀ i, s ≤ (splitRight w i).val ↔ stairHigh h s i :=
        fun i => (he i).symm.trans (hD i)
      simp [sameHighProjection, he, hD', stairHigh]
  · have hn : ¬ ((∀ i, s ≤ (splitLeft w i).val ↔ stairHigh h s i) ∧
        (∀ i, s ≤ (splitRight w i).val ↔ stairHigh h s i)) := by
      rintro ⟨h₁,h₂⟩
      exact he (fun i => (h₁ i).trans (h₂ i).symm)
    simp [sameHighProjection, he, hn]

lemma coordinateProjection_tensor {n d e : ℕ}
    (P : (Fin n → Fin d) → Prop) (Q : (Fin n → Fin e) → Prop)
    (x : WordSpace n d) (y : WordSpace n e) :
    coordinateProjection (fun w => P (splitLeft w) ∧ Q (splitRight w))
      (wordTensor n d e (x ⊗ₜ[ℂ] y)) =
    wordTensor n d e (coordinateProjection P x ⊗ₜ[ℂ] coordinateProjection Q y) := by
  classical
  ext w
  by_cases hp : P (splitLeft w) <;> by_cases hq : Q (splitRight w) <;>
    simp [hp,hq]

lemma altWord_sector_rotated {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (Q : Fin d → Prop) (D : Fin n → Prop) (r : G)
    (ha : ∀ i, Q ((a ∘ (r : Equiv.Perm (Fin n))) i) ↔ D i) :
    coordinateProjection (fun b => ∀ i, Q (b i) ↔ D i) (altWord G a) =
      signC (r : Equiv.Perm (Fin n)) • altWord (G ⊓ sectorGroup D) (a ∘ (r : Equiv.Perm (Fin n))) := by
  have hh := altWord_sector G (a ∘ (r : Equiv.Perm (Fin n))) Q D ha
  rw [altWord_move, map_smul] at hh
  rw [← hh, smul_smul, signC_mul_self, one_smul]

lemma polytabloid_eq_altWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t = altWord (columnGroup t) (rowWord t) := rfl

/- The cut's two layers, with their exact retained row and column permutations. -/
def cutRowWord (h s : ℕ) :=
  altWord (columnGroup (stairRowTableau (h+s)) ⊓ sectorGroup (stairHigh h s))
    (rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _))

def cutColumnWord (h s : ℕ) :=
  altWord (columnGroup (stairTableau (h+s)) ⊓ sectorGroup (stairHigh h s))
    (rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _))

lemma rotatePositions_sign (h s : ℕ) :
    signC (rotateColumnPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) =
      signC (rotateRowPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) := by
  let q : Equiv.Perm (Fin (staircase (h+s)).card) :=
    ((stairTableau (h+s)).trans (staircaseSwap (h+s))).trans (stairTableau (h+s)).symm
  have he : (rotateColumnPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) =
      q * (rotateRowPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) * q := by
    ext i
    simp [q, rotateColumnPositions, rotateRowPositions, rotateColumn]
  rw [he, map_mul, map_mul]
  calc
    signC q * signC (rotateRowPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) * signC q =
      signC (rotateRowPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) * (signC q * signC q) := by ring
    _ = _ := by rw [signC_mul_self, mul_one]

/- Exact sign cancellation in the two retained layers. -/
theorem staircase_cut_layers (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) =
      wordTensor _ _ _ (cutRowWord h s ⊗ₜ[ℂ] cutColumnWord h s) := by
  rw [staircase_projected_sector, staircaseWord]
  rw [coordinateProjection_tensor
    (fun a : Fin (staircase (h+s)).card → Fin ((staircase (h+s)).colLen 0) =>
      ∀ i, s ≤ (a i).val ↔ stairHigh h s i)
    (fun a : Fin (staircase (h+s)).card → Fin ((staircase (h+s)).colLen 0) =>
      ∀ i, s ≤ (a i).val ↔ stairHigh h s i)]
  have hr := altWord_sector_rotated (columnGroup (stairRowTableau (h+s)))
    (rowWord (stairRowTableau (h+s))) (fun a => s ≤ a.val) (stairHigh h s)
    (rotateRowPositions h s) (by
      intro i
      simpa [rowWord, stairRowTableau, rotateRowPositions, stairHigh, staircaseSwap] using
        rotateRow_high h s (stairTableau (h+s) i))
  have hc := altWord_sector_rotated (columnGroup (stairTableau (h+s)))
    (rowWord (stairTableau (h+s))) (fun a => s ≤ a.val) (stairHigh h s)
    (rotateColumnPositions h s) (by
      intro i
      simpa [rowWord, rotateColumnPositions, stairHigh] using
        rotateColumn_high h s (stairTableau (h+s) i))
  rw [polytabloid_eq_altWord, polytabloid_eq_altWord, hr, hc]
  rw [TensorProduct.smul_tmul_smul, rotatePositions_sign, signC_mul_self, one_smul]
  rfl

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl
/- The genuine product position permutation under a disjoint-set enumeration. -/
def sumPerm {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) : Equiv.Perm (Fin n) :=
  e.symm.permCongr (Equiv.sumCongr g h)

lemma signC_sumPerm {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
    signC (sumPerm e g h) = signC g * signC h := by
  simp [signC_def, sumPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

@[simp] lemma sumPerm_left {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) (i : Fin a) :
    sumPerm e g h (e.symm (Sum.inl i)) = e.symm (Sum.inl (g i)) := by
  simp [sumPerm, Equiv.permCongr_apply]

@[simp] lemma sumPerm_right {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) (i : Fin b) :
    sumPerm e g h (e.symm (Sum.inr i)) = e.symm (Sum.inr (h i)) := by
  simp [sumPerm, Equiv.permCongr_apply]

def leftWord {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) (w : Fin n → Fin d) : Fin a → Fin d :=
  fun i => w (e.symm (Sum.inl i))

def rightWord {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) (w : Fin n → Fin d) : Fin b → Fin d :=
  fun i => w (e.symm (Sum.inr i))

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

def positionProduct {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : WordSpace a d) (y : WordSpace b d) : WordSpace n d :=
  fun w => x (leftWord e w) * y (rightWord e w)

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



def fiberGroup {n : ℕ} {α : Type uAlpha} (f : Fin n → α) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ i, f (g i) = f i}
  one_mem' _ := rfl
  mul_mem' hg hh i := (hg _).trans (hh i)
  inv_mem' := by
    intro g hg i
    simpa using (hg (g⁻¹ i)).symm

def leftPositions {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Fin a ≃ {i : Fin n // (e i).isLeft = true} where
  toFun i := ⟨e.symm (Sum.inl i), by simp⟩
  invFun i := (e i.val).getLeft i.property
  left_inv i := by simp
  right_inv i := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Sum.inl_getLeft _ _

def rightPositions {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Fin b ≃ {i : Fin n // ¬(e i).isLeft = true} where
  toFun i := ⟨e.symm (Sum.inr i), by simp⟩
  invFun i := (e i.val).getRight (by
    have hi := i.property
    cases h : e i.val <;> simp_all)
  left_inv i := by simp
  right_inv i := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Sum.inr_getRight _ _

def leftRestriction {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) : Equiv.Perm (Fin a) :=
  (leftPositions e).symm.permCongr ((g : Equiv.Perm (Fin n)).subtypePerm g.property)

def rightRestriction {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) : Equiv.Perm (Fin b) :=
  (rightPositions e).symm.permCongr ((g : Equiv.Perm (Fin n)).subtypePerm (fun i => not_congr (g.property i)))

lemma leftRestriction_apply {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) (i : Fin a) :
    e.symm (Sum.inl (leftRestriction e g i)) = g.val (e.symm (Sum.inl i)) := by
  apply e.injective
  simp only [Equiv.apply_symm_apply]
  exact Sum.inl_getLeft _ _

lemma rightRestriction_apply {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) (i : Fin b) :
    e.symm (Sum.inr (rightRestriction e g i)) = g.val (e.symm (Sum.inr i)) := by
  apply e.injective
  simp only [Equiv.apply_symm_apply]
  exact Sum.inr_getRight _ _

lemma sumPerm_restrictions {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) :
    sumPerm e (leftRestriction e g) (rightRestriction e g) = g.val := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j => simpa using leftRestriction_apply e g j
  | inr j => simpa using rightRestriction_apply e g j

lemma sumPerm_injective {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Function.Injective (fun p : Equiv.Perm (Fin a) × Equiv.Perm (Fin b) => sumPerm e p.1 p.2) := by
  intro p q hpq
  apply Prod.ext
  · apply Equiv.ext
    intro i
    have h := congrArg (fun g : Equiv.Perm (Fin n) => e (g (e.symm (Sum.inl i)))) hpq
    simpa using h
  · apply Equiv.ext
    intro i
    have h := congrArg (fun g : Equiv.Perm (Fin n) => e (g (e.symm (Sum.inr i)))) hpq
    simpa using h

def fiberSplit {n a b : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin n → α) :
    (fiberGroup (fun i => f (e.symm (Sum.inl i)))) × (fiberGroup (fun i => f (e.symm (Sum.inr i)))) ≃
      ↥(fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true)) := by
  let F : (fiberGroup (fun i => f (e.symm (Sum.inl i)))) ×
      (fiberGroup (fun i => f (e.symm (Sum.inr i)))) →
      ↥(fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true)) := fun p =>
    ⟨sumPerm e p.1.val p.2.val, by
      constructor
      · intro i
        obtain ⟨j,rfl⟩ := e.symm.surjective i
        cases j with
        | inl j => simpa using p.1.property j
        | inr j => simpa using p.2.property j
      · intro i
        obtain ⟨j,rfl⟩ := e.symm.surjective i
        cases j <;> simp⟩
  apply Equiv.ofBijective F
  constructor
  · intro p q hpq
    have hh : sumPerm e p.1.val p.2.val = sumPerm e q.1.val q.2.val := congrArg Subtype.val hpq
    have h := @sumPerm_injective n a b e (p.1.val,p.2.val) (q.1.val,q.2.val) hh
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  · intro g
    let g' : sectorGroup (fun i => (e i).isLeft = true) := ⟨g.val,g.property.2⟩
    refine ⟨(⟨leftRestriction e g', ?_⟩, ⟨rightRestriction e g', ?_⟩), ?_⟩
    · intro i
      dsimp only
      rw [leftRestriction_apply]
      exact g.property.1 _
    · intro i
      dsimp only
      rw [rightRestriction_apply]
      exact g.property.1 _
    · exact Subtype.ext (sumPerm_restrictions e g')

lemma fiberSplit_apply {n a b : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin n → α)
    (p : (fiberGroup (fun i => f (e.symm (Sum.inl i)))) × (fiberGroup (fun i => f (e.symm (Sum.inr i))))) :
    (fiberSplit e f p).val = sumPerm e p.1.val p.2.val := rfl

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


@[simp] lemma staircase_colLen (m j : ℕ) : (staircase m).colLen j = m-j := by
  have hh : ∀ i, i < (staircase m).colLen j ↔ i < m-j := by
    intro i
    rw [← YoungDiagram.mem_iff_lt_colLen, mem_staircase]
    omega
  have h₁ := hh ((staircase m).colLen j)
  have h₂ := hh (m-j)
  omega

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

def highPositionsEquiv (h s : ℕ) :
    {i : Fin (staircase (h+s)).card // stairHigh h s i} ≃ Fin (staircase h).card where
  toFun i := (stairTableau h).symm ⟨(stairTableau (h+s) i.val).val, mem_staircase.mpr i.property⟩
  invFun j := ⟨(stairTableau (h+s)).symm ⟨(stairTableau h j).val, by
    apply mem_staircase.mpr
    have := mem_staircase.mp (stairTableau h j).property
    omega⟩, by
      change ((stairTableau (h+s)) ((stairTableau (h+s)).symm _)).val.1 +
        ((stairTableau (h+s)) ((stairTableau (h+s)).symm _)).val.2 < h
      simp only [Equiv.apply_symm_apply]
      exact mem_staircase.mp (stairTableau h j).property⟩
  left_inv i := by apply Subtype.ext; simp
  right_inv i := by simp

abbrev bandSize (h s : ℕ) := Nat.card {i : Fin (staircase (h+s)).card // ¬stairHigh h s i}

def cutPositions (h s : ℕ) :
    Fin (staircase (h+s)).card ≃ Fin (staircase h).card ⊕ Fin (bandSize h s) := by
  classical
  exact (Equiv.sumCompl (stairHigh h s)).symm.trans
    (Equiv.sumCongr (highPositionsEquiv h s) (Fintype.equivFinOfCardEq (show Fintype.card {i : Fin (staircase (h+s)).card // ¬stairHigh h s i} = bandSize h s from Fintype.card_eq_nat_card)))

lemma cutPositions_high (h s : ℕ) (i : Fin (staircase (h+s)).card) :
    (cutPositions h s i).isLeft = true ↔ stairHigh h s i := by
  classical
  by_cases hi : stairHigh h s i <;> simp [cutPositions, Equiv.sumCompl, Equiv.sumCongr, hi]

lemma cutPositions_left (h s : ℕ) (i : Fin (staircase h).card) :
    (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val = (stairTableau h i).val := by
  classical
  simp [cutPositions, Equiv.sumCompl, highPositionsEquiv]

lemma bandSize_add (h s : ℕ) : (staircase h).card + bandSize h s = (staircase (h+s)).card := by
  have hh := Fintype.card_congr (cutPositions h s)
  simpa using hh.symm

def bandTableau (h s : ℕ) (j : Fin (bandSize h s)) : (staircase (h+s)).cells :=
  stairTableau (h+s) ((cutPositions h s).symm (Sum.inr j))

def bandRowGroup (h s : ℕ) := fiberGroup (fun j => (bandTableau h s j).val.1)
def bandColumnGroup (h s : ℕ) := fiberGroup (fun j => (bandTableau h s j).val.2)

def highLetter (h s : ℕ) : Fin ((staircase h).colLen 0) → Fin ((staircase (h+s)).colLen 0) :=
  fun a => ⟨a.val+s, by have := a.isLt; simp only [staircase_colLen, Nat.sub_zero] at *; omega⟩

def letterLift {n d e : ℕ} (f : Fin d → Fin e) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n e) :=
  wordMap (fun a b => if f a = b then 1 else 0)

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

def bandRowWord (h s : ℕ) : WordSpace (bandSize h s) ((staircase (h+s)).colLen 0) :=
  altWord (bandRowGroup h s) (rightWord (cutPositions h s)
    (rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _)))

def bandColumnWord (h s : ℕ) : WordSpace (bandSize h s) ((staircase (h+s)).colLen 0) :=
  altWord (bandColumnGroup h s) (rightWord (cutPositions h s)
    (rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _)))

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



lemma bandTableau_bounds (h s : ℕ) (j : Fin (bandSize h s)) :
    h ≤ (bandTableau h s j).val.1 + (bandTableau h s j).val.2 ∧
      (bandTableau h s j).val.1 + (bandTableau h s j).val.2 < h+s := by
  refine ⟨?_,mem_staircase.mp (bandTableau h s j).property⟩
  have hh := cutPositions_high h s ((cutPositions h s).symm (Sum.inr j))
  simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, false_iff] at hh
  change ¬ (bandTableau h s j).val.1 + (bandTableau h s j).val.2 < h at hh
  omega

def bandCellsEquiv (h s : ℕ) : Fin (bandSize h s) ≃
    {c : ℕ × ℕ // h ≤ c.1+c.2 ∧ c.1+c.2 < h+s} :=
  Equiv.ofBijective (fun j => ⟨(bandTableau h s j).val,bandTableau_bounds h s j⟩) (by
    constructor
    · intro i j hij
      have hh : bandTableau h s i = bandTableau h s j := Subtype.ext (congrArg (fun c : {c : ℕ × ℕ // h ≤ c.1+c.2 ∧ c.1+c.2 < h+s} => c.val) hij)
      exact Sum.inr.inj ((cutPositions h s).symm.injective ((stairTableau (h+s)).injective hh))
    · intro c
      let x : (staircase (h+s)).cells := ⟨c.val,mem_staircase.mpr c.property.2⟩
      let i := (stairTableau (h+s)).symm x
      have hi : ¬ stairHigh h s i := by
        change ¬ (stairTableau (h+s) ((stairTableau (h+s)).symm x)).val.1 +
          (stairTableau (h+s) ((stairTableau (h+s)).symm x)).val.2 < h
        simp only [Equiv.apply_symm_apply]
        exact Nat.not_lt.mpr c.property.1
      have he := cutPositions_high h s i
      cases hp : cutPositions h s i with
      | inl j => simp only [hp, Sum.isLeft_inl, true_iff] at he; exact False.elim (hi he)
      | inr j =>
        refine ⟨j, ?_⟩
        apply Subtype.ext
        have hj : (cutPositions h s).symm (Sum.inr j) = i := by rw [← hp,Equiv.symm_apply_apply]
        change (stairTableau (h+s) ((cutPositions h s).symm (Sum.inr j))).val = c.val
        rw [hj]
        exact congrArg Subtype.val ((stairTableau (h+s)).apply_symm_apply x))

def pathCellsEquiv (h : ℕ) : Fin (2*(h+1)+1) ≃
    {c : ℕ × ℕ // h ≤ c.1+c.2 ∧ c.1+c.2 < h+2} where
  toFun k := ⟨(h+1-(k.val+1)/2,k.val/2), by have := k.isLt; omega⟩
  invFun c := ⟨h+1-c.val.1+c.val.2, by have := c.property; omega⟩
  left_inv k := by apply Fin.ext; dsimp; have := k.isLt; omega
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> have := c.property <;> omega

/- The exact path order, starting at the bottom row singleton and ending
at the rightmost column singleton. -/
def bandPathEquiv (h : ℕ) : Fin (2*(h+1)+1) ≃ Fin (bandSize h 2) :=
  (pathCellsEquiv h).trans (bandCellsEquiv h 2).symm

lemma bandPath_coordinates (h : ℕ) (k : Fin (2*(h+1)+1)) :
    (bandTableau h 2 (bandPathEquiv h k)).val = (h+1-(k.val+1)/2,k.val/2) := by
  have hh := (bandCellsEquiv h 2).apply_symm_apply (pathCellsEquiv h k)
  exact congrArg Subtype.val hh

lemma bandPath_card (h : ℕ) : bandSize h 2 = 2*(h+1)+1 := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (bandPathEquiv h)).symm

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl.PathLayer

def tag {r : ℕ} (i : Fin (2*r+1)) : ℕ := (i.val+1)/2

def base {r : ℕ} (i : Fin (2*r+1)) : Fin 2 := if i.val=0 then 0 else ⟨(i.val+1)%2, Nat.mod_lt _ (by omega)⟩

def rowAlt (r : ℕ) : Saxl.WordSpace (2*r+1) 2 :=
  Saxl.altWord (Saxl.fiberGroup (@tag r)) (@base r)

def appendPair (r : ℕ) : Fin (2*(r+1)+1) ≃ Fin (2*r+1) ⊕ Fin 2 :=
  (finCongr (by omega : 2*(r+1)+1 = (2*r+1)+2)).trans finSumFinEquiv.symm

@[simp] lemma appendPair_left (r : ℕ) (i : Fin (2*r+1)) :
    ((appendPair r).symm (Sum.inl i)).val = i.val := rfl
@[simp] lemma appendPair_right (r : ℕ) (i : Fin 2) :
    ((appendPair r).symm (Sum.inr i)).val = 2*r+1+i.val := rfl

lemma tag_left (r : ℕ) (i : Fin (2*r+1)) :
    tag ((appendPair r).symm (Sum.inl i)) = tag i := rfl
lemma tag_right (r : ℕ) (i : Fin 2) :
    tag ((appendPair r).symm (Sum.inr i)) = r+1 := by
  unfold tag
  rw [appendPair_right]
  omega

lemma tag_side (r : ℕ) (i : Fin (2*(r+1)+1)) :
    (appendPair r i).isLeft = true ↔ tag i < r+1 := by
  obtain ⟨j,rfl⟩ := (appendPair r).symm.surjective i
  cases j with
  | inl j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, true_iff, tag_left]; unfold tag; omega
  | inr j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, tag_right, lt_self_iff_false]

lemma rowGroup_sector (r : ℕ) :
    Saxl.fiberGroup (@tag (r+1)) = Saxl.fiberGroup (@tag (r+1)) ⊓
      Saxl.sectorGroup (fun i => (appendPair r i).isLeft = true) := by
  apply le_antisymm
  · intro g hg
    refine ⟨hg, ?_⟩
    intro i
    change (appendPair r (g i)).isLeft = true ↔ (appendPair r i).isLeft = true
    rw [tag_side,tag_side]
    change ∀ i, tag (g i) = tag i at hg
    rw [hg]
  · exact inf_le_left

lemma rowAlt_step (r : ℕ) :
    rowAlt (r+1) = Saxl.positionProduct (appendPair r) (rowAlt r)
      (Saxl.altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i)) := by
  unfold rowAlt
  rw [rowGroup_sector, Saxl.altWord_fiber_split]
  have hl : Saxl.fiberGroup (fun i => tag ((appendPair r).symm (Sum.inl i))) =
      Saxl.fiberGroup (@tag r) := rfl
  have hr : Saxl.fiberGroup (fun i => tag ((appendPair r).symm (Sum.inr i))) = ⊤ := by
    apply Subgroup.ext
    intro g
    change (∀ i, tag ((appendPair r).symm (Sum.inr (g i))) = tag ((appendPair r).symm (Sum.inr i))) ↔ True
    simp only [tag_right, implies_true]
  rw [hl,hr]
  congr 2
  funext i
  apply Fin.ext
  change (base ((appendPair r).symm (Sum.inr i))).val = i.val
  have hn : ((appendPair r).symm (Sum.inr i)).val ≠ 0 := by rw [appendPair_right]; omega
  unfold base
  rw [ite_eq_right hn]
  change (2*r+1+i.val+1)%2 = i.val
  omega

def J : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;-1,0]

lemma pair_alt (w : Fin 2 → Fin 2) :
    Saxl.altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i) w = J (w 0) (w 1) := by
  classical
  let := Fintype.ofFinite (⊤ : Subgroup (Equiv.Perm (Fin 2)))
  unfold Saxl.altWord
  rw [Finset.sum_apply]
  change (∑ g : (⊤ : Subgroup (Equiv.Perm (Fin 2))), Saxl.signC (g : Equiv.Perm (Fin 2)) *
    ((Pi.single (fun i : Fin 2 => i) (1:ℂ) : Saxl.WordSpace 2 2) (w ∘ (g : Equiv.Perm (Fin 2))))) = _
  calc
    _ = ∑ g : Equiv.Perm (Fin 2), Saxl.signC g *
        ((Pi.single (fun i : Fin 2 => i) (1:ℂ) : Saxl.WordSpace 2 2) (w ∘ g)) :=
      Fintype.sum_equiv (Subgroup.topEquiv (G := Equiv.Perm (Fin 2))).toEquiv _ _ (by intro g; rfl)
    _ = _ := by
      have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1,Equiv.swap 0 1} := by decide
      rw [hu]
      have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
      simp only [Finset.sum_insert (Finset.notMem_singleton.mpr hne), Finset.sum_singleton]
      have hw : w = ![w 0,w 1] := by ext i; fin_cases i <;> rfl
      rw [hw]
      generalize h0 : w 0 = a
      generalize h1 : w 1 = b
      fin_cases a <;> fin_cases b <;>
        norm_num [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J]

lemma rowAlt_zero (w : Fin 1 → Fin 2) :
    rowAlt 0 w = if w 0 = 0 then 1 else 0 := by
  classical
  change Saxl.altWord (Saxl.fiberGroup (@tag 0)) (@base 0) w = _
  let := Fintype.ofFinite (Saxl.fiberGroup (@tag 0))
  unfold Saxl.altWord
  have hu : (Finset.univ : Finset (Saxl.fiberGroup (@tag 0))) = {1} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Fin.ext
    have := ((g : Equiv.Perm (Fin (2*0+1))) i).isLt
    have := i.isLt
    omega
  rw [hu,Finset.sum_singleton]
  simp only [OneMemClass.coe_one, map_one, one_smul]
  change (Pi.single (@base 0) (1:ℂ) : Saxl.WordSpace 1 2) w = _
  rw [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; have := congrFun h 0; simpa [base] using this
  · intro h; funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; simpa [base] using h

lemma rowAlt_formula (r : ℕ) (w : Fin (2*r+1) → Fin 2) :
    rowAlt r w = (if w 0 = 0 then 1 else 0) *
      ∏ i : Fin r, J (w ⟨2*i.val+1,by omega⟩) (w ⟨2*i.val+2,by omega⟩) := by
  induction r with
  | zero => simpa using rowAlt_zero w
  | succ r ih =>
    rw [rowAlt_step]
    change rowAlt r (Saxl.leftWord (appendPair r) w) *
      Saxl.altWord ⊤ (fun i : Fin 2 => i) (Saxl.rightWord (appendPair r) w) = _
    rw [ih, pair_alt, Fin.prod_univ_castSucc]
    exact mul_assoc _ _ _

end Saxl.PathLayer

namespace Saxl

def fiberRelabel {n m : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin m) (c : Fin m → α) :
    fiberGroup (c ∘ e) ≃ fiberGroup c where
  toFun g := ⟨e.permCongr g.val, by
    intro i
    obtain ⟨j,rfl⟩ := e.surjective i
    change c (e (g.val (e.symm (e j)))) = c (e j)
    rw [Equiv.symm_apply_apply]
    exact g.property j⟩
  invFun g := ⟨e.symm.permCongr g.val, by
    intro i
    change c (e (e.symm (g.val (e i)))) = c (e i)
    rw [Equiv.apply_symm_apply]
    exact g.property (e i)⟩
  left_inv g := by apply Subtype.ext; ext i; simp [Equiv.permCongr]
  right_inv g := by apply Subtype.ext; ext i; simp [Equiv.permCongr]

lemma altWord_fiber_relabel {n m d : ℕ} {α : Type uAlpha}
    (e : Fin n ≃ Fin m) (c : Fin m → α) (a : Fin m → Fin d) (w : Fin n → Fin d) :
    altWord (fiberGroup c) a (w ∘ e.symm) =
      altWord (fiberGroup (c ∘ e)) (a ∘ e) w := by
  classical
  let := Fintype.ofFinite (fiberGroup c)
  let := Fintype.ofFinite (fiberGroup (c ∘ e))
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  apply Fintype.sum_equiv (fiberRelabel e c)
  intro g
  have hs : signC ((fiberRelabel e c g).val) = signC g.val := by
    change signC (e.permCongr g.val) = _
    simp only [signC_def, Equiv.Perm.sign_permCongr]
  rw [hs]
  congr 1
  change (Pi.single (a ∘ e) (1:ℂ) : WordSpace n d) (w ∘ g.val) =
    (Pi.single a (1:ℂ) : WordSpace m d) ((w ∘ e.symm) ∘ (e.permCongr g.val))
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    simpa [Equiv.permCongr] using congrFun h j
  · intro h
    funext i
    simpa [Equiv.permCongr] using congrFun h (e i)

lemma altWord_letter_eval {n d D : ℕ} (φ : Fin d → Fin D) (hφ : Function.Injective φ)
    (G : Subgroup (Equiv.Perm (Fin n))) (a w : Fin n → Fin d) :
    altWord G (φ ∘ a) (φ ∘ w) = altWord G a w := by
  classical
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro g hg
  congr 1
  change (Pi.single (φ ∘ a) (1:ℂ) : WordSpace n D) ((φ ∘ w) ∘ g.val) =
    (Pi.single a (1:ℂ) : WordSpace n d) (w ∘ g.val)
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; funext i; exact hφ (congrFun h i)
  · intro h; funext i; exact congrArg φ (congrFun h i)



def lowLetter (h : ℕ) : Fin 2 → Fin ((staircase (h+2)).colLen 0) :=
  fun i => ⟨i.val, by rw [staircase_colLen]; have := i.isLt; omega⟩

lemma lowLetter_injective (h : ℕ) : Function.Injective (lowLetter h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin ((staircase (h+2)).colLen 0) => x.val) hij)

def bandColumnPathEquiv (h : ℕ) : Fin (2*(h+1)+1) ≃ Fin (bandSize h 2) :=
  Fin.revPerm.trans (bandPathEquiv h)

lemma bandColumnPath_coordinates (h : ℕ) (k : Fin (2*(h+1)+1)) :
    (bandTableau h 2 (bandColumnPathEquiv h k)).val = (k.val/2,h+1-(k.val+1)/2) := by
  change (bandTableau h 2 (bandPathEquiv h k.rev)).val = _
  rw [bandPath_coordinates]
  apply Prod.ext <;> simp only [Fin.val_rev] <;> have := k.isLt <;> omega

lemma bandRow_path_group (h : ℕ) :
    fiberGroup ((fun j => (bandTableau h 2 j).val.1) ∘ bandPathEquiv h) =
      fiberGroup (@PathLayer.tag (h+1)) := by
  apply Subgroup.ext
  intro g
  change (∀ i, _ = _) ↔ (∀ i, _ = _)
  simp only [Function.comp_apply, bandPath_coordinates, PathLayer.tag]
  constructor <;> intro hg i <;> have hh := hg i <;>
    have := i.isLt <;> have := (g i).isLt <;> omega

lemma bandColumn_path_group (h : ℕ) :
    fiberGroup ((fun j => (bandTableau h 2 j).val.2) ∘ bandColumnPathEquiv h) =
      fiberGroup (@PathLayer.tag (h+1)) := by
  apply Subgroup.ext
  intro g
  change (∀ i, _ = _) ↔ (∀ i, _ = _)
  simp only [Function.comp_apply, bandColumnPath_coordinates, PathLayer.tag]
  constructor <;> intro hg i <;> have hh := hg i <;>
    have := i.isLt <;> have := (g i).isLt <;> omega

lemma bandRow_path_base (h : ℕ) :
    (rightWord (cutPositions h 2)
      (rowWord (stairRowTableau (h+2)) ∘ (rotateRowPositions h 2 : Equiv.Perm _))) ∘ bandPathEquiv h =
      lowLetter h ∘ (@PathLayer.base (h+1)) := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, rightWord, rowWord, stairRowTableau, rotateRowPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply, staircaseSwap]
  change (rotateRow h 2 (bandTableau h 2 (bandPathEquiv h k))).val.2 = _
  change (if (bandTableau h 2 (bandPathEquiv h k)).val.2 < h-(bandTableau h 2 (bandPathEquiv h k)).val.1 then
    (bandTableau h 2 (bandPathEquiv h k)).val.2+2 else
    (bandTableau h 2 (bandPathEquiv h k)).val.2-(h-(bandTableau h 2 (bandPathEquiv h k)).val.1)) = _
  rw [bandPath_coordinates]
  simp only [lowLetter, PathLayer.base]
  split_ifs <;> have := k.isLt <;> simp only [Fin.val_zero] <;> omega

lemma bandColumn_path_base (h : ℕ) :
    (rightWord (cutPositions h 2)
      (rowWord (stairTableau (h+2)) ∘ (rotateColumnPositions h 2 : Equiv.Perm _))) ∘ bandColumnPathEquiv h =
      lowLetter h ∘ (@PathLayer.base (h+1)) := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, rightWord, rowWord, rotateColumnPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply]
  change (rotateColumn h 2 (bandTableau h 2 (bandColumnPathEquiv h k))).val.1 = _
  change (if (bandTableau h 2 (bandColumnPathEquiv h k)).val.1 < h-(bandTableau h 2 (bandColumnPathEquiv h k)).val.2 then
    (bandTableau h 2 (bandColumnPathEquiv h k)).val.1+2 else
    (bandTableau h 2 (bandColumnPathEquiv h k)).val.1-(h-(bandTableau h 2 (bandColumnPathEquiv h k)).val.2)) = _
  rw [bandColumnPath_coordinates]
  simp only [lowLetter, PathLayer.base]
  split_ifs <;> have := k.isLt <;> simp only [Fin.val_zero] <;> omega

lemma bandRow_path_eval (h : ℕ) (w : Fin (2*(h+1)+1) → Fin 2) :
    bandRowWord h 2 ((lowLetter h ∘ w) ∘ (bandPathEquiv h).symm) = PathLayer.rowAlt (h+1) w := by
  unfold bandRowWord bandRowGroup
  rw [altWord_fiber_relabel, bandRow_path_group, bandRow_path_base,
    altWord_letter_eval _ (lowLetter_injective h)]
  rfl

lemma bandColumn_path_eval (h : ℕ) (w : Fin (2*(h+1)+1) → Fin 2) :
    bandColumnWord h 2 ((lowLetter h ∘ w) ∘ (bandColumnPathEquiv h).symm) = PathLayer.rowAlt (h+1) w := by
  unfold bandColumnWord bandColumnGroup
  rw [altWord_fiber_relabel, bandColumn_path_group, bandColumn_path_base,
    altWord_letter_eval _ (lowLetter_injective h)]
  rfl

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl.Band
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def basis (i : ℕ) : Mat :=
  match i with
  | 0 => 1
  | 1 => !![1, 0; 0, -1]
  | 2 => !![0, 1; 1, 0]
  | _ => !![0, 1; -1, 0]

def D (q : ℕ) (X : Mat) : Mat := if q % 2 = 0 then X.adjugate else X

def segment (r p : ℕ) : Mat :=
  ∑ π : Equiv.Perm (Fin r),
    ((((Equiv.Perm.sign π) : ℤ) : ℂ)) •
      (List.ofFn (fun j : Fin r => D (p + j.val) (basis (π j).val))).prod

/- Consecutive segments with the original global position parities. -/
def blocks : ℕ → List ℕ → Mat
  | _, [] => 1
  | p, r :: rs => segment r p * blocks (p + r) rs

/- Enumeration of the finite symmetric group for the four small matrix calculations. -/
lemma sum_perm_succ {A : Type uA} [AddCommMonoid A] (n : ℕ)
    (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ π, f π) = ∑ i : Fin (n + 1), ∑ σ : Equiv.Perm (Fin n),
      f (Equiv.Perm.decomposeFin.symm (i, σ)) := by
  calc
    (∑ π, f π) = ∑ x : Fin (n + 1) × Equiv.Perm (Fin n),
        f (Equiv.Perm.decomposeFin.symm x) :=
      Fintype.sum_equiv Equiv.Perm.decomposeFin _ _ (by intro π; simp)
    _ = _ := Fintype.sum_prod_type _

lemma decompose_apply_two {n : ℕ} (e : Equiv.Perm (Fin (n + 2))) (p : Fin (n + 3)) :
    Equiv.Perm.decomposeFin.symm (p, e) 2 = Equiv.swap 0 p (e 1).succ := by
  change Equiv.Perm.decomposeFin.symm (p, e) (1 : Fin (n + 2)).succ = _
  exact Equiv.Perm.decomposeFin_symm_apply_succ e p 1

lemma decompose_apply_three {n : ℕ} (e : Equiv.Perm (Fin (n + 3))) (p : Fin (n + 4)) :
    Equiv.Perm.decomposeFin.symm (p, e) 3 = Equiv.swap 0 p (e 2).succ := by
  change Equiv.Perm.decomposeFin.symm (p, e) (2 : Fin (n + 3)).succ = _
  exact Equiv.Perm.decomposeFin_symm_apply_succ e p 2

lemma segment_one_even : segment 1 0 = 1 := by
  simp [segment, List.ofFn_succ, basis, D]

lemma segment_one_odd : segment 1 1 = 1 := by
  simp [segment, List.ofFn_succ, basis, D]

lemma segment_two_even : segment 2 0 = (2 : ℂ) • basis 1 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_two_odd : segment 2 1 = (-2 : ℂ) • basis 1 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_three_even : segment 3 0 = (-6 : ℂ) • basis 3 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_three_odd : segment 3 1 = (-6 : ℂ) • basis 3 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_four_even : segment 4 0 = (24 : ℂ) • basis 0 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_four_odd : segment 4 1 = (-24 : ℂ) • basis 0 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/- Only the original global parity matters. -/
lemma segment_mod (r p : ℕ) : segment r p = segment r (p % 2) := by
  simp [segment, D, Nat.add_mod]

def ScaledBasis (X : Mat) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∃ i : Fin 4, X = c • basis i.val

lemma scaledBasis_smul (c : ℂ) (hc : c ≠ 0) (i : Fin 4) :
    ScaledBasis (c • basis i.val) := ⟨c, hc, i, rfl⟩

lemma scaledBasis_one : ScaledBasis 1 := by
  exact ⟨1, one_ne_zero, 0, by simp [basis]⟩

lemma basis_mul (i j : Fin 4) : ScaledBasis (basis i.val * basis j.val) := by
  fin_cases i <;> fin_cases j
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]

lemma ScaledBasis.mul {X Y : Mat} (hX : ScaledBasis X) (hY : ScaledBasis Y) :
    ScaledBasis (X * Y) := by
  obtain ⟨c, hc, i, rfl⟩ := hX
  obtain ⟨d, hd, j, rfl⟩ := hY
  obtain ⟨e, he, k, hk⟩ := basis_mul i j
  refine ⟨c * d * e, mul_ne_zero (mul_ne_zero hc hd) he, k, ?_⟩
  rw [smul_mul_smul_comm, hk, smul_smul]

lemma segment_scaled (r p : ℕ) (hr : 1 ≤ r ∧ r ≤ 4) : ScaledBasis (segment r p) := by
  rw [segment_mod]
  have hp := Nat.mod_two_eq_zero_or_one p
  obtain ⟨hr1, hr4⟩ := hr
  interval_cases r <;> rcases hp with hp | hp <;> rw [hp]
  all_goals simp only [segment_one_even, segment_one_odd,
    segment_two_even, segment_two_odd, segment_three_even, segment_three_odd,
    segment_four_even, segment_four_odd]
  all_goals first
    | exact scaledBasis_one
    | exact scaledBasis_smul _ (by norm_num) 0
    | exact scaledBasis_smul _ (by norm_num) 1
    | exact scaledBasis_smul _ (by norm_num) 3

lemma blocks_scaled (rs : List ℕ) (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) (p : ℕ) :
    ScaledBasis (blocks p rs) := by
  induction rs generalizing p with
  | nil => exact scaledBasis_one
  | cons r rs ih =>
    exact (segment_scaled r p (hrs r (by simp))).mul
      (ih (fun a ha => hrs a (by simp [ha])) (p + r))

def Q : Mat := !![1, 1; 1, 2]
def Qinv : Mat := !![2, -1; -1, 1]

lemma Q_mul_Qinv : Q * Qinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two]

lemma Qinv_mul_Q : Qinv * Q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two]

lemma Q_isUnit : IsUnit Q := ⟨⟨Q, Qinv, Q_mul_Qinv, Qinv_mul_Q⟩, rfl⟩

lemma Q_inverse : Q⁻¹ = Qinv := by
  exact Matrix.inv_eq_left_inv Qinv_mul_Q

lemma Q_basis_ne_zero (i : Fin 4) : (Q * basis i.val * Q⁻¹) 0 0 ≠ 0 := by
  rw [Q_inverse]
  fin_cases i <;> norm_num [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two]

/- Endpoint noncancellation for arbitrary consecutive columns of lengths at most four. -/
theorem band_nonzero_pairing (rs : List ℕ)
    (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) :
    ∃ Q : Mat, IsUnit Q ∧ (Q * blocks 1 rs * Q⁻¹) 0 0 ≠ 0 := by
  obtain ⟨c, hc, i, hi⟩ := blocks_scaled rs hrs 1
  refine ⟨Q, Q_isUnit, ?_⟩
  rw [hi, Matrix.mul_smul, Matrix.smul_mul]
  exact mul_ne_zero hc (Q_basis_ne_zero i)

end Saxl.Band

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Path
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Letter := Fin 4

def parts (x : Letter) : Fin 2 × Fin 2 := finProdFinEquiv.symm x
def J : Mat := !![0, 1; -1, 0]

def leftPos {r : ℕ} (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val, by omega⟩
def midPos {r : ℕ} (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val + 1, by omega⟩
def rightPos {r : ℕ} (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val + 2, by omega⟩

/- EXACT coefficients of the path-ordered alternating band: the two endpoint
singletons carry letter 0, and row/column pairs have coefficients J. Here r=m-1. -/
def bandWord (r : ℕ) (w : Fin (2 * r + 1) → Letter) : ℂ :=
  (if (parts (w 0)).1 = 0 then 1 else 0) *
  (if (parts (w (Fin.last (2 * r)))).2 = 0 then 1 else 0) *
  ∏ i : Fin r, J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
    J (parts (w (midPos i))).1 (parts (w (rightPos i))).1

/- Ordinary pure position tensor pairing, with no conjugation. -/
def pureWord {n : ℕ} (X : Fin n → Mat) (w : Fin n → Letter) : ℂ :=
  ∏ i, X i (parts (w i)).1 (parts (w i)).2

def entry (a : Letter) : Mat := Matrix.single (parts a).1 (parts a).2 1

def DL (q : ℕ) : Mat →ₗ[ℂ] Mat where
  toFun := Band.D q
  map_add' X Y := by
    by_cases h : q % 2 = 0
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Band.D, h, Matrix.adjugate_fin_two, add_comm]
    · simp [Band.D, h]
  map_smul' c X := by
    by_cases h : q % 2 = 0
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Band.D, h, Matrix.adjugate_fin_two]
    · simp [Band.D, h]

def chainML (n p : ℕ) : MultilinearMap ℂ (fun _ : Fin n => Mat) Mat :=
  (MultilinearMap.mkPiAlgebraFin ℂ n Mat).compLinearMap (fun i => DL (p + i.val))

lemma chainML_apply (n p : ℕ) (X : Fin n → Mat) :
    chainML n p X = (List.ofFn fun i => Band.D (p + i.val) (X i)).prod := rfl

lemma entry_sum (X : Mat) :
    (∑ a : Letter, X (parts a).1 (parts a).2 • entry a) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]

lemma chain_expand (n p : ℕ) (X : Fin n → Mat) :
    chainML n p X = ∑ w : Fin n → Letter, pureWord X w •
      chainML n p (fun i => entry (w i)) := by
  calc
    chainML n p X = chainML n p (fun i => ∑ a : Letter,
      X i (parts a).1 (parts a).2 • entry a) := by
        congr 1; funext i; exact (entry_sum (X i)).symm
    _ = _ := ?_
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [MultilinearMap.map_smul_univ]
  rfl

lemma adj_entry (a : Letter) (i j : Fin 2) :
    (entry a).adjugate i j = -(J i (parts a).2 * J (parts a).1 j) := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]

lemma D_shift (q : ℕ) (X : Mat) : Band.D (q + 2) X = Band.D q X := by
  simp [Band.D]

lemma chain_step (r : ℕ) (w : Fin (2 * (r+1) + 1) → Letter) :
    chainML (2 * (r+1) + 1) 1 (fun i => entry (w i)) =
      entry (w 0) * (entry (w 1)).adjugate *
      chainML (2 * r + 1) 1 (fun i => entry (w i.succ.succ)) := by
  rw [chainML_apply, List.ofFn_succ, List.prod_cons, List.ofFn_succ,
    List.prod_cons, chainML_apply]
  simp only [Fin.val_zero, Fin.val_succ, add_zero]
  rw [show Band.D 1 = id from by funext X; simp [Band.D],
    show Band.D 2 = Matrix.adjugate from by funext X; simp [Band.D]]
  simp only [id_eq]
  rw [mul_assoc]
  apply congrArg (fun A : Mat => entry (w 0) * ((entry (w 1)).adjugate * A))
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  rw [show 1 + (i.val + 1 + 1) = (1 + i.val) + 2 by omega, D_shift]

lemma pair_product_step (r : ℕ) (w : Fin (2 * (r+1) + 1) → Letter) :
    (∏ i : Fin (r+1), J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
      J (parts (w (midPos i))).1 (parts (w (rightPos i))).1) =
    (J (parts (w 0)).2 (parts (w 1)).2 * J (parts (w 1)).1 (parts (w 2)).1) *
    ∏ i : Fin r, J (parts (w (leftPos i).succ.succ)).2
      (parts (w (midPos i).succ.succ)).2 *
      J (parts (w (midPos i).succ.succ)).1 (parts (w (rightPos i).succ.succ)).1 := by
  rw [Fin.prod_univ_succ]
  rfl

lemma chain_entries (r : ℕ) (w : Fin (2*r+1) → Letter) :
    chainML (2*r+1) 1 (fun i => entry (w i)) =
    ((-1 : ℂ)^r * ∏ i : Fin r,
      J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
      J (parts (w (midPos i))).1 (parts (w (rightPos i))).1) •
    Matrix.single (parts (w 0)).1 (parts (w (Fin.last (2*r)))).2 1 := by
  induction r with
  | zero => simp [chainML_apply, List.ofFn_succ, Band.D, entry]
  | succ r ih =>
    rw [chain_step, ih, Matrix.mul_smul, pair_product_step]
    rw [show (0 : Fin (2*r+1)).succ.succ = 2 from Fin.ext rfl]
    change _ = _ • Matrix.single _ (parts (w (Fin.last (2*r)).succ.succ)).2 1
    unfold entry at *
    rw [Matrix.single_mul_mul_single, one_mul, mul_one]
    rw [show (Matrix.single (parts (w 1)).1 (parts (w 1)).2 (1 : ℂ)).adjugate
      (parts (w 0)).2 (parts (w 2)).1 =
      -(J (parts (w 0)).2 (parts (w 1)).2 * J (parts (w 1)).1 (parts (w 2)).1)
      from adj_entry (w 1) _ _]
    rw [show ∀ (c : ℂ) (i j : Fin 2), Matrix.single i j c = c • Matrix.single i j 1
      from fun c i j => by ext a b; simp [Matrix.single, smul_eq_mul]]
    rw [smul_smul]
    congr 1
    rw [pow_succ]
    ring

lemma chain_entries_endpoint (r : ℕ) (w : Fin (2*r+1) → Letter) :
    chainML (2*r+1) 1 (fun i => entry (w i)) 0 0 =
      (-1 : ℂ)^r * bandWord r w := by
  rw [chain_entries]
  by_cases h₁ : (parts (w 0)).1 = 0 <;>
    by_cases h₂ : (parts (w (Fin.last (2*r)))).2 = 0 <;>
    simp [bandWord, Matrix.single, h₁, h₂]

theorem path_contraction (r : ℕ) (X : Fin (2*r+1) → Mat) :
    dotProduct (bandWord r) (pureWord X) =
      (-1 : ℂ)^r * (List.ofFn fun q => Band.D (1+q.val) (X q)).prod 0 0 := by
  have h := congrArg (fun A : Mat => A 0 0) (chain_expand (2*r+1) 1 X)
  change chainML (2*r+1) 1 X 0 0 =
    (∑ w : Fin (2*r+1) → Letter,
      pureWord X w • chainML (2*r+1) 1 (fun i => entry (w i))) 0 0 at h
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    chain_entries_endpoint] at h
  rw [← chainML_apply, h, Finset.mul_sum]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro w hw
  have hs : (-1 : ℂ)^r * (-1 : ℂ)^r = 1 := by
    rw [← mul_pow]; norm_num
  calc
    bandWord r w * pureWord X w =
        ((-1 : ℂ)^r * (-1 : ℂ)^r) * (bandWord r w * pureWord X w) := by rw [hs, one_mul]
    _ = _ := by ring

lemma J_real (i j : Fin 2) : star (J i j) = J i j := by
  fin_cases i <;> fin_cases j <;> simp [J]

lemma bandWord_real (r : ℕ) : star (bandWord r) = bandWord r := by
  funext w
  change star (bandWord r w) = bandWord r w
  by_cases h₁ : (parts (w 0)).1 = 0 <;>
    by_cases h₂ : (parts (w (Fin.last (2*r)))).2 = 0 <;>
    simp [bandWord, h₁, h₂, star_mul, star_prod, J_real, mul_comm]
end Saxl.Path

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/
@[reducible] def Cells : List ℕ → Type
  | [] => Empty
  | r :: rs => Fin r ⊕ Cells rs

instance cellsFintype : (rs : List ℕ) → Fintype (Cells rs)
  | [] => inferInstanceAs (Fintype Empty)
  | r :: rs => @instFintypeSum (Fin r) (Cells rs) inferInstance (cellsFintype rs)

instance cellsDecEq : (rs : List ℕ) → DecidableEq (Cells rs)
  | [] => inferInstanceAs (DecidableEq Empty)
  | r :: rs => @instDecidableEqSum (Fin r) (Cells rs) inferInstance (cellsDecEq rs)

def row : {rs : List ℕ} → Cells rs → ℕ
  | _ :: _, .inl i => i.val
  | _ :: _, .inr c => row c

def col : {rs : List ℕ} → Cells rs → ℕ
  | _ :: _, .inl _ => 0
  | _ :: _, .inr c => col c + 1

def enumerate : (rs : List ℕ) → Fin rs.sum ≃ Cells rs
  | [] => (Equiv.equivOfIsEmpty (Fin 0) Empty)
  | r :: rs => finSumFinEquiv.symm.trans ((Equiv.refl (Fin r)).sumCongr (enumerate rs))

@[simp] lemma enumerate_left (r : ℕ) (rs : List ℕ) (i : Fin r) :
    enumerate (r :: rs) (Fin.castAdd rs.sum i) = Sum.inl i := by
  exact congrArg ((Equiv.refl (Fin r)).sumCongr (enumerate rs))
    (finSumFinEquiv_symm_apply_castAdd i)

@[simp] lemma enumerate_right (r : ℕ) (rs : List ℕ) (i : Fin rs.sum) :
    enumerate (r :: rs) (Fin.natAdd r i) = Sum.inr (enumerate rs i) := by
  exact congrArg ((Equiv.refl (Fin r)).sumCongr (enumerate rs))
    (finSumFinEquiv_symm_apply_natAdd i)

@[reducible] def Perms : List ℕ → Type
  | [] => Unit
  | r :: rs => Equiv.Perm (Fin r) × Perms rs

instance permsFintype : (rs : List ℕ) → Fintype (Perms rs)
  | [] => inferInstanceAs (Fintype Unit)
  | r :: rs => @instFintypeProd (Equiv.Perm (Fin r)) (Perms rs) inferInstance (permsFintype rs)

def perm : {rs : List ℕ} → Perms rs → Equiv.Perm (Cells rs)
  | [], _ => Equiv.refl _
  | _ :: _, (π, σ) => Equiv.sumCongr π (perm σ)

def sg : {rs : List ℕ} → Perms rs → ℂ
  | [], _ => 1
  | _ :: _, (π, σ) => (((Equiv.Perm.sign π : ℤ) : ℂ)) * sg σ

lemma sign_perm {rs : List ℕ} (π : Perms rs) :
    (((Equiv.Perm.sign (perm π) : ℤ) : ℂ)) = sg π := by
  induction rs with
  | nil => simp [perm, sg]
  | cons r rs ih =>
    obtain ⟨π, σ⟩ := π
    have hh := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ))
      (Equiv.Perm.sign_sumCongr π (perm σ))
    exact hh.trans (by simp only [Units.val_mul, Int.cast_mul, ih]; rfl)

lemma perm_col {rs : List ℕ} (π : Perms rs) (c : Cells rs) : col (perm π c) = col c := by
  induction rs with
  | nil => exact isEmptyElim c
  | cons r rs ih =>
    obtain ⟨π, σ⟩ := π
    cases c with
    | inl i => rfl
    | inr c => exact congrArg (· + 1) (ih σ c)

lemma coords_injective (rs : List ℕ) :
    Function.Injective (fun c : Cells rs => (row c, col c)) := by
  induction rs with
  | nil => exact Function.injective_of_subsingleton _
  | cons r rs ih =>
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Fin.ext (congrArg Prod.fst h))
      | inr b => have := congrArg Prod.snd h; simp [col] at this
    | inr a =>
      cases b with
      | inl b => have := congrArg Prod.snd h; simp [col] at this
      | inr b =>
        apply congrArg Sum.inr
        apply ih
        dsimp only [row, col] at h
        have hr := congrArg Prod.fst h
        have hc := congrArg Prod.snd h
        exact Prod.ext hr (Nat.add_right_cancel hc)

lemma coords_range (rs : List ℕ) (i j : ℕ) :
    (∃ c : Cells rs, row c = i ∧ col c = j) ↔ ∃ h : j < rs.length, i < rs[j] := by
  induction rs generalizing j with
  | nil => simp [Cells]
  | cons r rs ih =>
    cases j with
    | zero =>
      constructor
      · rintro ⟨c, hr, hc⟩
        cases c with
        | inl a => exact ⟨by simp, by simpa [row] using hr ▸ a.isLt⟩
        | inr a => simp [col] at hc
      · rintro ⟨h, hi⟩
        exact ⟨Sum.inl ⟨i, hi⟩, rfl, rfl⟩
    | succ j =>
      constructor
      · rintro ⟨c, hr, hc⟩
        cases c with
        | inl a => simp [col] at hc
        | inr a =>
          have hj : col a = j := Nat.add_right_cancel hc
          obtain ⟨hj, hi⟩ := (ih j).mp ⟨a, hr, hj⟩
          exact ⟨Nat.succ_lt_succ hj, hi⟩
      · rintro ⟨h, hi⟩
        obtain ⟨a, ha, hc⟩ := (ih j).mpr ⟨Nat.lt_of_succ_lt_succ h, hi⟩
        exact ⟨Sum.inr a, ha, congrArg (· + 1) hc⟩

/- The matrix product indexed by the actual consecutive position order. -/
def chain (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat) (π : Perms rs) : Band.Mat :=
  (List.ofFn fun q : Fin rs.sum => Band.D (p + q.val) (N (row (perm π (enumerate rs q))))).prod

lemma chain_cons (r : ℕ) (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat)
    (π : Equiv.Perm (Fin r)) (σ : Perms rs) :
    chain (r :: rs) p N (π, σ) =
      (List.ofFn fun j : Fin r => Band.D (p + j.val) (N (π j).val)).prod *
      chain rs (p + r) N σ := by
  unfold chain
  erw [List.ofFn_add, List.prod_append]
  congr 2
  · apply congrArg List.ofFn
    funext j
    change Band.D (p + j.val) (N (row (@perm (r :: rs) (π, σ) (enumerate (r :: rs) (Fin.castAdd rs.sum j))))) = _
    rw [enumerate_left]
    rfl
  · apply congrArg List.ofFn
    funext j
    change Band.D (p + (r + j.val)) (N (row (@perm (r :: rs) (π, σ) (enumerate (r :: rs) (Fin.natAdd r j))))) = _
    erw [enumerate_right r rs (show Fin rs.sum from j)]
    simp only [perm, Equiv.sumCongr_apply, Sum.map_inr, row, Nat.add_assoc]

/- Ordered product of independent alternating column segments. -/
def segments : ℕ → List ℕ → (ℕ → Band.Mat) → Band.Mat
  | _, [], _ => 1
  | p, r :: rs, N =>
      (∑ π : Equiv.Perm (Fin r), (((Equiv.Perm.sign π : ℤ) : ℂ)) •
        (List.ofFn fun i : Fin r => Band.D (p + i.val) (N (π i).val)).prod) *
      segments (p+r) rs N

/- Factorization over independent column permutations, without commuting factors. -/
lemma sum_chain (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat) :
    (∑ π : Perms rs, sg π • chain rs p N π) = segments p rs N := by
  induction rs generalizing p with
  | nil => simp [Perms, chain, sg, segments]
  | cons r rs ih =>
    simp only [Perms, Fintype.sum_prod_type, sg, chain_cons, segments]
    simp_rw [← smul_mul_smul_comm, ← Finset.mul_sum, ← Finset.sum_mul, ih]

lemma perm_injective (rs : List ℕ) : Function.Injective (@perm rs) := by
  induction rs with
  | nil => exact Function.injective_of_subsingleton _
  | cons r rs ih =>
    rintro ⟨π, σ⟩ ⟨π', σ'⟩ h
    apply Prod.ext
    · apply Equiv.ext
      intro i
      exact Sum.inl.inj (Equiv.congr_fun h (Sum.inl i))
    · apply ih
      apply Equiv.ext
      intro c
      exact Sum.inr.inj (Equiv.congr_fun h (Sum.inr c))

lemma perm_surjective (rs : List ℕ) (g : Equiv.Perm (Cells rs))
    (hg : ∀ c, col (g c) = col c) : ∃ π : Perms rs, perm π = g := by
  induction rs with
  | nil => exact ⟨(), Subsingleton.elim _ _⟩
  | cons r rs ih =>
    have hm : Set.MapsTo g (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro c ⟨i, rfl⟩
      have hh := hg (Sum.inl i)
      cases h : g (Sum.inl i) with
      | inl j => exact ⟨j, rfl⟩
      | inr c => simp [h, col] at hh
    obtain ⟨⟨π, σ⟩, he⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hm
    have hs : ∀ c : Cells rs, col (σ c) = col c := by
      intro c
      have hh := hg (Sum.inr c)
      rw [← he] at hh
      exact Nat.add_right_cancel hh
    obtain ⟨τ, hτ⟩ := ih σ hs
    exact ⟨(π, τ), by simp only [perm, hτ]; exact he⟩

/- The column-recursive coordinates enumerate the actual Ferrers cells. -/
def toYoung (μ : YoungDiagram) : Cells μ.transpose.rowLens ≃ μ.cells := by
  let f : Cells μ.transpose.rowLens → μ.cells := fun c =>
    ⟨(row c, col c), by
      obtain ⟨hj, hi⟩ := (coords_range μ.transpose.rowLens (row c) (col c)).mp ⟨c, rfl, rfl⟩
      simpa only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen,
        YoungDiagram.get_rowLens, YoungDiagram.rowLen_transpose] using hi⟩
  exact Equiv.ofBijective f ⟨fun _ _ h => coords_injective _ (congrArg Subtype.val h), by
    intro c
    have hmem : c.val.1 < μ.colLen c.val.2 := YoungDiagram.mem_iff_lt_colLen.mp c.property
    have hj : c.val.2 < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp
      (μ.up_left_mem (Nat.zero_le _) le_rfl c.property)
    have hj' : c.val.2 < μ.transpose.rowLens.length := by simpa using hj
    obtain ⟨a, ha, hb⟩ := (coords_range μ.transpose.rowLens c.val.1 c.val.2).mpr
      ⟨hj', by simpa using hmem⟩
    exact ⟨a, Subtype.ext (Prod.ext ha hb)⟩⟩

@[simp] lemma toYoung_val (μ : YoungDiagram) (c : Cells μ.transpose.rowLens) :
    (toYoung μ c).val = (row c, col c) := rfl

lemma row_lt (μ : YoungDiagram) (c : Cells μ.transpose.rowLens) : row c < μ.colLen 0 :=
  YoungDiagram.mem_iff_lt_colLen.mp
    (μ.up_left_mem le_rfl (Nat.zero_le _) (toYoung μ c).property)


def columnTableau (μ : YoungDiagram) : Tableau μ.transpose.rowLens.sum μ :=
  (enumerate μ.transpose.rowLens).trans (toYoung μ)

@[simp] lemma columnTableau_val (μ : YoungDiagram) (i : Fin μ.transpose.rowLens.sum) :
    (columnTableau μ i).val = (row (enumerate μ.transpose.rowLens i),
      col (enumerate μ.transpose.rowLens i)) := rfl

def columnPerm (μ : YoungDiagram) (π : Perms μ.transpose.rowLens) :
    columnGroup (columnTableau μ) :=
  ⟨(enumerate μ.transpose.rowLens).symm.permCongr (perm π), by
    intro i
    simp only [columnTableau_val, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
    exact perm_col π _⟩

lemma columnPerm_bijective (μ : YoungDiagram) : Function.Bijective (columnPerm μ) := by
  constructor
  · intro π σ h
    apply perm_injective μ.transpose.rowLens
    apply (enumerate μ.transpose.rowLens).symm.permCongr.injective
    exact congrArg Subtype.val h
  · intro g
    let e := enumerate μ.transpose.rowLens
    obtain ⟨π, hπ⟩ := perm_surjective μ.transpose.rowLens (e.permCongr g.val) (by
      intro c
      have hh := g.property (e.symm c)
      simpa only [columnTableau_val, Equiv.permCongr_apply, e, Equiv.apply_symm_apply] using hh)
    refine ⟨π, ?_⟩
    apply Subtype.ext
    change e.symm.permCongr (perm π) = g.val
    rw [hπ]
    apply Equiv.ext
    intro i
    simp [Equiv.permCongr_apply]

def columnEquiv (μ : YoungDiagram) : Perms μ.transpose.rowLens ≃ columnGroup (columnTableau μ) :=
  Equiv.ofBijective (columnPerm μ) (columnPerm_bijective μ)

lemma columnPerm_sign (μ : YoungDiagram) (π : Perms μ.transpose.rowLens) :
    signC (columnPerm μ π).val = sg π := by
  change (((Equiv.Perm.sign ((enumerate μ.transpose.rowLens).symm.permCongr (perm π)) : ℤ) : ℂ)) = sg π
  rw [Equiv.Perm.sign_permCongr]
  exact sign_perm π

lemma mapped_columnTableau (μ : YoungDiagram) (N : ℕ → Band.Mat) :
    wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
      N i.val (Path.parts a).1 (Path.parts a).2) (polytabloid (columnTableau μ)) =
    ∑ π : Perms μ.transpose.rowLens, sg π • Path.pureWord
      (fun q => N (row (perm π (enumerate μ.transpose.rowLens q)))) := by
  classical
  let := Fintype.ofFinite (columnGroup (columnTableau μ))
  unfold polytabloid
  rw [map_sum]
  let e : Perms μ.transpose.rowLens ≃ columnGroup (columnTableau μ) :=
    (columnEquiv μ).trans (Equiv.inv _)
  symm
  apply Fintype.sum_equiv e
  intro π
  rw [map_smul, wordRep_single]
  have hs : signC (e π).val = sg π := by
    change signC (columnPerm μ π).val⁻¹ = sg π
    rw [signC_inv, columnPerm_sign]
  change sg π • _ = signC (e π).val • _
  rw [hs]
  congr 1
  funext w
  rw [wordMap_single]
  unfold Path.pureWord
  apply Finset.prod_congr rfl
  intro q hq
  have hr : row (perm π (enumerate μ.transpose.rowLens q)) =
      ((columnTableau μ) ((e π).val⁻¹ q)).val.1 := by
    change _ = ((columnTableau μ) (((columnPerm μ π).val⁻¹)⁻¹ q)).val.1
    rw [inv_inv, columnTableau_val]
    dsimp only [columnPerm, Equiv.permCongr_apply]
    rw [Equiv.apply_symm_apply, Equiv.symm_symm]
  exact congrArg (fun j => N j (Path.parts (w q)).1 (Path.parts (w q)).2) hr

end Saxl.Columns

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Band

def conjugation : Mat →ₗ[ℂ] Mat where
  toFun X := Q * X * Qinv
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

lemma conjugation_one : conjugation 1 = 1 := by
  change Q * 1 * Qinv = 1
  rw [mul_one, Q_mul_Qinv]

lemma conjugation_mul (X Y : Mat) : conjugation (X * Y) = conjugation X * conjugation Y := by
  change Q * (X * Y) * Qinv = (Q * X * Qinv) * (Q * Y * Qinv)
  simp only [mul_assoc, ← mul_assoc Qinv Q, Qinv_mul_Q, one_mul]

lemma conjugation_D (q : ℕ) (X : Mat) : D q (conjugation X) = conjugation (D q X) := by
  by_cases h : q % 2 = 0
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, h, conjugation, Q, Qinv, Matrix.adjugate_fin_two, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
  · simp [D, h]

lemma conjugation_prod (l : List Mat) : (l.map conjugation).prod = conjugation l.prod := by
  induction l with
  | nil => simp [conjugation_one]
  | cons a l ih => simp [ih, conjugation_mul]

lemma segments_conjugation (rs : List ℕ) (p : ℕ) :
    Columns.segments p rs (fun i => conjugation (basis i)) = conjugation (blocks p rs) := by
  induction rs generalizing p with
  | nil => exact conjugation_one.symm
  | cons r rs ih =>
    simp only [Columns.segments, blocks, ih, conjugation_mul]
    congr 1
    unfold segment
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro π hπ
    rw [map_smul]
    congr 1
    simp_rw [conjugation_D]
    have he := conjugation_prod (List.ofFn fun j : Fin r => D (p + j.val) (basis (π j).val))
    rw [List.map_ofFn] at he
    exact he

lemma conjugation_blocks_ne_zero (rs : List ℕ)
    (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) : conjugation (blocks 1 rs) 0 0 ≠ 0 := by
  obtain ⟨c, hc, i, hi⟩ := blocks_scaled rs hrs 1
  rw [hi, map_smul]
  apply mul_ne_zero hc
  simpa only [conjugation, LinearMap.coe_mk, AddHom.coe_mk, Q_inverse] using Q_basis_ne_zero i

end Saxl.Band
namespace Saxl.Path

def chainFunctional (n p : ℕ) : WordSpace n 4 →ₗ[ℂ] Mat where
  toFun x := ∑ w : Fin n → Fin 4, x w • chainML n p (fun i => entry (w i))
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [smul_smul, Finset.smul_sum]

lemma chainFunctional_pure (n p : ℕ) (X : Fin n → Mat) :
    chainFunctional n p (pureWord X) = chainML n p X := (chain_expand n p X).symm

lemma chainFunctional_column (μ : YoungDiagram) (p : ℕ) (N : ℕ → Mat) :
    chainFunctional μ.transpose.rowLens.sum p
      (wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
        N i.val (parts a).1 (parts a).2) (polytabloid (Columns.columnTableau μ))) =
      Columns.segments p μ.transpose.rowLens N := by
  rw [Columns.mapped_columnTableau, map_sum]
  simp_rw [map_smul, chainFunctional_pure]
  exact Columns.sum_chain μ.transpose.rowLens p N

lemma chainFunctional_endpoint (r : ℕ) (x : WordSpace (2*r+1) 4) :
    chainFunctional (2*r+1) 1 x 0 0 = (-1 : ℂ)^r * dotProduct x (bandWord r) := by
  change (∑ w : Fin (2*r+1) → Fin 4,
    x w • chainML (2*r+1) 1 (fun i => entry (w i))) 0 0 = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, chain_entries_endpoint]
  simp [dotProduct, Finset.mul_sum, mul_left_comm]


lemma fourRow_column_lengths (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ 4) :
    ∀ r ∈ μ.transpose.rowLens, 1 ≤ r ∧ r ≤ 4 := by
  intro r hr
  refine ⟨μ.transpose.pos_of_mem_rowLens r hr, ?_⟩
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hr
  rw [← he, YoungDiagram.get_rowLens, YoungDiagram.rowLen_transpose]
  exact (μ.colLen_anti 0 j (Nat.zero_le _)).trans hμ

lemma fourRow_tableau_noncancellation (n : ℕ) (μ : YoungDiagram)
    (hn : μ.transpose.rowLens.sum = n) (hμ : μ.colLen 0 ≤ 4) :
    ∃ s : Tableau n μ, chainFunctional n 1
      (wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
        Band.conjugation (Band.basis i.val) (parts a).1 (parts a).2) (polytabloid s)) 0 0 ≠ 0 := by
  subst n
  refine ⟨Columns.columnTableau μ, ?_⟩
  rw [chainFunctional_column μ 1 (fun i => Band.conjugation (Band.basis i)),
    Band.segments_conjugation]
  exact Band.conjugation_blocks_ne_zero _ (fourRow_column_lengths μ hμ)

/- The actual complex Specht modules with at most four rows occur in the
specified two-layer alternating path cyclic module. -/
theorem fourRow_support (r : ℕ) (_hr : 2 ≤ r) (μ : YoungDiagram)
    (t : Tableau (2*r+1) μ) (hμ : μ.colLen 0 ≤ 4) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*r+1) 4) (bandWord r)).toRepresentation, f ≠ 0 := by
  have hn : μ.transpose.rowLens.sum = 2*r+1 := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr ((Columns.columnTableau μ).trans t.symm)
  obtain ⟨s, hs⟩ := fourRow_tableau_noncancellation (2*r+1) μ hn hμ
  let L : Fin (μ.colLen 0) → Fin 4 → ℂ := fun i a =>
    Band.conjugation (Band.basis i.val) (parts a).1 (parts a).2
  apply hom_to_cyclic_of_pair L (spechtSub t)
    ⟨polytabloid s, polytabloid_mem_all t s⟩ (bandWord r) (bandWord_real r)
  intro h
  rw [chainFunctional_endpoint] at hs
  exact hs (by change (-1 : ℂ)^r * dotProduct (wordMap L (polytabloid s)) (bandWord r) = 0
               rw [h, mul_zero])

end Saxl.Path

namespace Saxl.PathLayer

lemma J_flip (a b : Fin 2) : J a b = - J b a := by
  fin_cases a <;> fin_cases b <;> norm_num [J]

lemma rowAlt_rev_formula (r : ℕ) (w : Fin (2*r+1) → Fin 2) :
    rowAlt r (w ∘ Fin.rev) = (if w (Fin.last (2*r)) = 0 then 1 else 0) *
      ((-1 : ℂ)^r * ∏ i : Fin r, J (w ⟨2*i.val,by omega⟩) (w ⟨2*i.val+1,by omega⟩)) := by
  rw [rowAlt_formula]
  have hzero : (0 : Fin (2*r+1)).rev = Fin.last (2*r) := by apply Fin.ext; simp
  simp only [Function.comp_apply, hzero]
  congr 1
  calc
    (∏ i : Fin r, J (w (⟨2*i.val+1,by omega⟩ : Fin (2*r+1)).rev)
      (w (⟨2*i.val+2,by omega⟩ : Fin (2*r+1)).rev)) =
      ∏ i : Fin r, (-1 : ℂ) * J (w ⟨2*i.val,by omega⟩) (w ⟨2*i.val+1,by omega⟩) := by
        apply Fintype.prod_equiv Fin.revPerm
        intro i
        have h₁ : (⟨2*i.val+1,by omega⟩ : Fin (2*r+1)).rev = ⟨2*i.rev.val+1,by omega⟩ := by
          apply Fin.ext; simp only [Fin.val_rev]; have := i.isLt; omega
        have h₂ : (⟨2*i.val+2,by omega⟩ : Fin (2*r+1)).rev = ⟨2*i.rev.val,by omega⟩ := by
          apply Fin.ext; simp only [Fin.val_rev]; have := i.isLt; omega
        rw [h₁,h₂,J_flip]
        simp
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

theorem paired_rowAlt (r : ℕ) (w : Fin (2*r+1) → Saxl.Path.Letter) :
    rowAlt r (fun i => (Saxl.Path.parts (w i)).1) *
      rowAlt r ((fun i => (Saxl.Path.parts (w i)).2) ∘ Fin.rev) =
      (-1 : ℂ)^r * Saxl.Path.bandWord r w := by
  rw [rowAlt_formula,rowAlt_rev_formula]
  unfold Saxl.Path.bandWord
  rw [Finset.prod_mul_distrib]
  change _ = (-1:ℂ)^r * (_ * _ *
    ((∏ i : Fin r, J (Saxl.Path.parts (w ⟨2*i.val,by omega⟩)).2 (Saxl.Path.parts (w ⟨2*i.val+1,by omega⟩)).2) *
     (∏ i : Fin r, J (Saxl.Path.parts (w ⟨2*i.val+1,by omega⟩)).1 (Saxl.Path.parts (w ⟨2*i.val+2,by omega⟩)).1)))
  ring

end Saxl.PathLayer

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

/- Explicit finite-group induction on a linear map. -/
def averagedMap {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) (f : X →ₗ[ℂ] Y) :
    Representation.IntertwiningMap ρ σ where
  toLinearMap := ∑ g : G, (σ g).comp (f.comp (ρ g⁻¹))
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
    rw [map_sum]
    apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
    apply Finset.sum_congr rfl
    intro g hg
    change σ (h*g) (f (ρ (h*g)⁻¹ (ρ h x))) = σ h (σ g (f (ρ g⁻¹ x)))
    simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
    have he : ρ h⁻¹ (ρ h x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [he]

lemma averagedMap_apply {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) (f : X →ₗ[ℂ] Y) (x : X) :
    averagedMap ρ σ f x = ∑ g : G, σ g (f (ρ g⁻¹ x)) := by
  simp only [averagedMap, Representation.IntertwiningMap.coe_mk, LinearMap.sum_apply,
    LinearMap.comp_apply]

/- Coordinate-sector induction, in precisely the nonzero-Hom form used in
the staircase induction. The projector kills translates outside the stabilizer. -/
theorem sector_average_nonzero {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y)
    (H : Subgroup G) (f : X →ₗ[ℂ] Y) (hf : f ≠ 0)
    (he : ∀ g ∈ H, ∀ x, f (ρ g x) = σ g (f x))
    (P : Y →ₗ[ℂ] Y) (hP : ∀ x, P (f x) = f x)
    (hkill : ∀ g ∉ H, ∀ x, P (σ g (f x)) = 0) :
    averagedMap ρ σ f ≠ 0 := by
  classical
  have hproj (x : X) : P (averagedMap ρ σ f x) =
      ((Finset.univ.filter (fun g : G => g ∈ H)).card : ℂ) • f x := by
    rw [averagedMap_apply, map_sum]
    have hh (g : G) : P (σ g (f (ρ g⁻¹ x))) = if g ∈ H then f x else 0 := by
      by_cases hg : g ∈ H
      · rw [ite_eq_left hg, ← he g hg, ← Module.End.mul_apply, ← map_mul,
          mul_inv_cancel, map_one]
        exact hP x
      · rw [ite_eq_right hg]
        exact hkill g hg _
    simp only [hh]
    simp [Finset.sum_ite, Nat.cast_smul_eq_nsmul]
  have hc : ((Finset.univ.filter (fun g : G => g ∈ H)).card : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact ne_of_gt (Finset.card_pos.mpr ⟨1, by simp⟩)
  intro hz
  apply hf
  ext x
  have heq := hproj x
  rw [hz] at heq
  change P 0 = _ at heq
  rw [map_zero] at heq
  exact (smul_eq_zero.mp heq.symm).resolve_left hc

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

def wordSector {n d : ℕ} (D : Fin n → Prop) (A : Fin d → Prop)
    (w : Fin n → Fin d) : Prop := ∀ i, A (w i) ↔ D i

/- Concrete sector averaging produces a constituent of the full cyclic
module from an equivariant map on its coordinate sector. -/
theorem sector_support_transfer {n d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (D : Fin n → Prop) (A : Fin d → Prop) (z : WordSpace n d)
    (f : X →ₗ[ℂ] WordSpace n d) (hf : f ≠ 0)
    (he : ∀ g ∈ sectorGroup D, ∀ x, f (ρ g x) = wordRep n d g (f x))
    (hm : ∀ x, f x ∈ cyclic (wordRep n d) z)
    (hs : ∀ x w, f x w ≠ 0 → wordSector D A w) :
    ∃ F : Representation.IntertwiningMap ρ (cyclic (wordRep n d) z).toRepresentation,
      F ≠ 0 := by
  classical
  let P := coordinateProjection (wordSector D A)
  have hP (x) : P (f x) = f x := by
    ext w
    change (if wordSector D A w then f x w else 0) = _
    split_ifs with h
    · rfl
    · exact (not_ne_iff.mp (fun hh => h (hs x w hh))).symm
  have hk (g : Equiv.Perm (Fin n)) (hg : g ∉ sectorGroup D) (x) :
      P (wordRep n d g (f x)) = 0 := by
    ext w
    change (if wordSector D A w then f x (w ∘ g) else 0) = 0
    split_ifs with hw
    · by_contra hn
      have hh := hs x (w ∘ g) hn
      apply hg
      intro i
      exact (hw (g i)).symm.trans (hh i)
    · rfl
  let F := averagedMap ρ (wordRep n d) f
  have hF : F ≠ 0 := sector_average_nonzero ρ (wordRep n d) (sectorGroup D) f hf he P hP hk
  have hmem (x) : F x ∈ cyclic (wordRep n d) z := by
    rw [show F x = _ from averagedMap_apply ρ (wordRep n d) f x]
    apply Submodule.sum_mem
    intro g hg
    exact (cyclic (wordRep n d) z).apply_mem_toSubmodule g (hm _)
  let G : Representation.IntertwiningMap ρ (cyclic (wordRep n d) z).toRepresentation :=
    { toLinearMap := F.toLinearMap.codRestrict _ hmem
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact LinearMap.congr_fun (F.isIntertwining' g) x }
  refine ⟨G, ?_⟩
  intro hz
  apply hF
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (congrArg (fun l => l x) hz)

lemma intertwiner_cyclic_mem {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (v : X) (x : X) (hx : x ∈ cyclic ρ v) :
    F x ∈ cyclic σ (F v) := by
  change x ∈ Submodule.span ℂ _ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    change F (ρ g v) ∈ _
    have hF : F (ρ g v) = σ g (F v) := LinearMap.congr_fun (F.isIntertwining' g) v
    rw [hF]
    exact (cyclic σ (F v)).apply_mem_toSubmodule g (mem_cyclic _ _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

def cyclicMap {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (v : X) :
    Representation.IntertwiningMap (cyclic ρ v).toRepresentation (cyclic σ (F v)).toRepresentation where
  toLinearMap := (F.toLinearMap.comp (cyclic ρ v).toSubmodule.subtype).codRestrict _
    (fun x => intertwiner_cyclic_mem F v x.val x.property)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (F.isIntertwining' g) x.val

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



lemma cyclic_smul_eq {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (c : ℂ) (hc : c ≠ 0) :
    cyclic ρ (c • v) = cyclic ρ v := by
  apply le_antisymm
  · apply (cyclic_le _ _ _).mpr
    exact Submodule.smul_mem _ _ (mem_cyclic ρ v)
  · apply (cyclic_le _ _ _).mpr
    have hh := Submodule.smul_mem (cyclic ρ (c • v)).toSubmodule c⁻¹ (mem_cyclic ρ (c • v))
    change v ∈ (cyclic ρ (c • v)).toSubmodule
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

lemma cyclic_action_eq {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (g : G) : cyclic ρ (ρ g v) = cyclic ρ v := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr ((cyclic ρ v).apply_mem_toSubmodule g (mem_cyclic ρ v))
  · apply (cyclic_le _ _ _).mpr
    have hh := (cyclic ρ (ρ g v)).apply_mem_toSubmodule g⁻¹ (mem_cyclic ρ (ρ g v))
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at hh
    exact hh

lemma support_relabel {n m d k : ℕ} (e : Fin n ≃ Fin m) (v : WordSpace n d)
    (hv : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t) (cyclic (wordRep n d) v).toRepresentation, f ≠ 0) :
    ∀ (μ : YoungDiagram) (t : Tableau m μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        (cyclic (wordRep m d) (fun w => v (w ∘ e))).toRepresentation, f ≠ 0 := by
  have hnm : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst m
  intro μ t hμ
  change ∃ f : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (wordRep n d e v)).toRepresentation, f ≠ 0
  rw [cyclic_action_eq]
  exact hv μ t hμ

def restrictLetters {n d D : ℕ} (φ : Fin d → Fin D) :
    Representation.IntertwiningMap (wordRep n D) (wordRep n d) where
  toLinearMap :=
    { toFun := fun x w => x (φ ∘ w)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  isIntertwining' g := by ext x w; rfl

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

def stairBandWord (h s : ℕ) : WordSpace (bandSize h s)
    ((staircase (h+s)).colLen 0 * (staircase (h+s)).colLen 0) :=
  wordTensor _ _ _ (bandRowWord h s ⊗ₜ[ℂ] bandColumnWord h s)

def lowPairLetter (h : ℕ) (x : Fin 4) :
    Fin ((staircase (h+2)).colLen 0 * (staircase (h+2)).colLen 0) :=
  finProdFinEquiv (lowLetter h (Path.parts x).1, lowLetter h (Path.parts x).2)

lemma bandColumn_path_eval' (h : ℕ) (w : Fin (2*(h+1)+1) → Fin 2) :
    bandColumnWord h 2 ((lowLetter h ∘ w) ∘ (bandPathEquiv h).symm) =
      PathLayer.rowAlt (h+1) (w ∘ Fin.rev) := by
  have he : (lowLetter h ∘ (w ∘ Fin.rev)) ∘ (bandColumnPathEquiv h).symm =
      (lowLetter h ∘ w) ∘ (bandPathEquiv h).symm := by
    funext i
    simp [bandColumnPathEquiv, Function.comp_def, Fin.revPerm]
  rw [← he, bandColumn_path_eval]

lemma stairBandWord_path_eval (h : ℕ) (w : Fin (2*(h+1)+1) → Fin 4) :
    restrictLetters (lowPairLetter h) (stairBandWord h 2) (w ∘ (bandPathEquiv h).symm) =
      (-1 : ℂ)^(h+1) * Path.bandWord (h+1) w := by
  change wordTensor _ _ _ (bandRowWord h 2 ⊗ₜ[ℂ] bandColumnWord h 2)
    (lowPairLetter h ∘ (w ∘ (bandPathEquiv h).symm)) = _
  rw [wordTensor_tmul]
  have hl : splitLeft (lowPairLetter h ∘ (w ∘ (bandPathEquiv h).symm)) =
      (lowLetter h ∘ (fun i => (Path.parts (w i)).1)) ∘ (bandPathEquiv h).symm := by
    funext i; simp [splitLeft, lowPairLetter]
  have hr : splitRight (lowPairLetter h ∘ (w ∘ (bandPathEquiv h).symm)) =
      (lowLetter h ∘ (fun i => (Path.parts (w i)).2)) ∘ (bandPathEquiv h).symm := by
    funext i; simp [splitRight, lowPairLetter]
  rw [hl,hr,bandRow_path_eval,bandColumn_path_eval']
  exact PathLayer.paired_rowAlt _ w

/- Every Specht shape with at most four rows occurs in the cyclic module
generated by the prescribed two-band vector. -/
theorem twoBand_support (h : ℕ) (hh : 1 ≤ h) (μ : YoungDiagram)
    (t : Tableau (bandSize h 2) μ) (hμ : μ.colLen 0 ≤ 4) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep _ _) (stairBandWord h 2)).toRepresentation, f ≠ 0 := by
  have he : restrictLetters (lowPairLetter h) (stairBandWord h 2) =
      (-1 : ℂ)^(h+1) • (fun w => Path.bandWord (h+1) (w ∘ bandPathEquiv h)) := by
    funext w
    have hw : (w ∘ bandPathEquiv h) ∘ (bandPathEquiv h).symm = w := by funext i; simp
    simpa only [hw,Pi.smul_apply,smul_eq_mul] using stairBandWord_path_eval h (w ∘ bandPathEquiv h)
  have hs := support_relabel (bandPathEquiv h) (Path.bandWord (h+1))
    (fun ν s hν => Path.fourRow_support (h+1) (by omega) ν s hν) μ t hμ
  have hc : cyclic (wordRep (bandSize h 2) 4) (restrictLetters (lowPairLetter h) (stairBandWord h 2)) =
      cyclic (wordRep (bandSize h 2) 4) (fun w => Path.bandWord (h+1) (w ∘ bandPathEquiv h)) := by
    rw [he,cyclic_smul_eq _ _ _ (pow_ne_zero _ (by norm_num))]
  rw [← hc] at hs
  obtain ⟨f,hf⟩ := hs
  exact cyclic_projection_support (restrictLetters (lowPairLetter h)) (stairBandWord h 2) f hf

end Saxl

namespace Saxl

/- Coordinate subrepresentation using only letters with property A. -/
def alphabetSub (n d : ℕ) (A : Fin d → Prop) : Subrepresentation (wordRep n d) where
  toSubmodule :=
    { carrier := {x | ∀ w, (∃ i, ¬ A (w i)) → x w = 0}
      zero_mem' := by intro w hw; rfl
      add_mem' := by intro x y hx hy w hw; change x w+y w=0; rw [hx w hw,hy w hw,add_zero]
      smul_mem' := by intro c x hx w hw; change c*x w=0; rw [hx w hw,mul_zero] }
  apply_mem_toSubmodule g := by
    intro x hx w hw
    obtain ⟨i,hi⟩ := hw
    apply hx (w ∘ g)
    exact ⟨g⁻¹ i, by simpa using hi⟩

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

lemma cyclic_alphabet {n d : ℕ} (A : Fin d → Prop) (v : WordSpace n d)
    (hv : v ∈ alphabetSub n d A) (x : WordSpace n d) (hx : x ∈ cyclic (wordRep n d) v) :
    x ∈ alphabetSub n d A := (cyclic_le _ _ _).mpr hv hx

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

lemma letterLift_eval {n d D : ℕ} (φ : Fin d → Fin D) (hφ : Function.Injective φ)
    (x : WordSpace n d) (w : Fin n → Fin d) : letterLift φ x (φ ∘ w) = x w := by
  classical
  change (∑ a, x a * ∏ i, (if φ (a i) = φ (w i) then (1:ℂ) else 0)) = x w
  rw [Finset.sum_eq_single w]
  · simp
  · intro a ha haw
    apply mul_eq_zero_of_right
    obtain ⟨i,hi⟩ : ∃ i, a i ≠ w i := by by_contra hh; push Not at hh; exact haw (funext hh)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right (fun hh => hi (hφ hh))
  · simp

lemma letterLift_injective {n d D : ℕ} (φ : Fin d → Fin D) (hφ : Function.Injective φ) :
    Function.Injective (letterLift (n := n) φ) := by
  intro x y hxy
  funext w
  have hh := congrFun hxy (φ ∘ w)
  simpa only [letterLift_eval φ hφ] using hh

def pairLift {n d D : ℕ} (φ : Fin d → Fin D) :
    Representation.IntertwiningMap (wordRep n (d*d)) (wordRep n (D*D)) :=
  (wordTensorIntertwiner _ _ _).comp (((letterLift φ).tensor (letterLift φ)).comp
    ((wordTensorIntertwiner n d d).ofBijective (wordTensor n d d).bijective).symm.toIntertwiningMap)

lemma pairLift_wordTensor {n d D : ℕ} (φ : Fin d → Fin D) (x y : WordSpace n d) :
    pairLift φ (wordTensor n d d (x ⊗ₜ[ℂ] y)) =
      wordTensor n D D (letterLift φ x ⊗ₜ[ℂ] letterLift φ y) := by
  let E := (wordTensorIntertwiner n d d).ofBijective (wordTensor n d d).bijective
  change wordTensor n D D (((letterLift φ).tensor (letterLift φ)) (E.symm (E (x ⊗ₜ[ℂ] y)))) = _
  rw [E.symm_apply_apply]
  rfl

lemma pairLift_injective {n d D : ℕ} (φ : Fin d → Fin D) (hφ : Function.Injective φ) :
    Function.Injective (pairLift (n := n) φ) := by
  apply (wordTensor n D D).injective.comp
  apply (TensorProduct.map_injective_of_flat_flat _ _ (letterLift_injective φ hφ) (letterLift_injective φ hφ)).comp
  exact ((wordTensorIntertwiner n d d).ofBijective (wordTensor n d d).bijective).symm.injective

lemma pairWord_mem_alphabetLeft {n d : ℕ} (A : Fin d → Prop)
    (x y : WordSpace n d) (hx : x ∈ alphabetSub n d A) :
    wordTensor n d d (x ⊗ₜ[ℂ] y) ∈
      alphabetSub n (d*d) (fun a => A (finProdFinEquiv.symm a).1) := by
  apply (alphabetSub_iff _ _).mpr
  intro w hw i
  rw [wordTensor_tmul] at hw
  exact (alphabetSub_iff A x).mp hx (splitLeft w) ((mul_ne_zero_iff.mp hw).1) i



def shiftedStairWord (h s : ℕ) := pairLift (highLetter h s) (staircaseWord h)

lemma highLetter_injective (h s : ℕ) : Function.Injective (highLetter h s) := by
  intro a b hab
  apply Fin.ext
  have := congrArg Fin.val hab
  dsimp [highLetter] at this
  omega

lemma shiftedStairWord_support (h s : ℕ) (μ : YoungDiagram) (t : Tableau (staircase h).card μ)
    (f : Representation.IntertwiningMap (spechtRep t) (staircaseCyclic h).toRepresentation)
    (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep _ _) (shiftedStairWord h s)).toRepresentation, F ≠ 0 := by
  let F := (cyclicMap (pairLift (highLetter h s)) (staircaseWord h)).comp f
  refine ⟨F, ?_⟩
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply pairLift_injective (highLetter h s) (highLetter_injective h s)
  have hh := congrArg (fun l => (l x).val) hz
  exact hh.trans (map_zero _).symm

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
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

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

/- Zero-based row-index statistic of a partition. -/
def rowMoment (μ : YoungDiagram) : ℤ := ∑ c ∈ μ.cells, (c.1 : ℤ)

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

/- The column operator on any genuine representation of the same group. -/
def columnOperator {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) : Module.End ℂ V := by
  classical
  letI := Fintype.ofFinite (columnGroup t)
  exact ∑ g : columnGroup t, signC (g : Equiv.Perm (Fin n)) • ρ g

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

/- Distinct genuine complex Specht shapes are inequivalent. -/
theorem specht_shape_rigidity {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν)
    (e : Representation.Equiv (spechtRep t) (spechtRep u)) : μ = ν := by
  obtain ⟨g, hg⟩ := mixed_injective_of_equiv t u e
  obtain ⟨h, hh⟩ := mixed_injective_of_equiv u t e.symm
  exact shapes_eq_of_mixed t u g hg
    (le_antisymm (mixed_moment_le t u g hg) (mixed_moment_le u t h hh))

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

/- Rows enumerate exactly the actual cells, including the empty diagram. -/
def rowCellEquiv (μ : YoungDiagram) : μ.cells ≃ (i : Fin (μ.colLen 0)) × Fin (μ.rowLen i) where
  toFun c := ⟨⟨c.val.1, YoungDiagram.mem_iff_lt_colLen.mp
      (μ.up_left_mem le_rfl (Nat.zero_le _) c.property)⟩,
    ⟨c.val.2, YoungDiagram.mem_iff_lt_rowLen.mp c.property⟩⟩
  invFun c := ⟨(c.1.val, c.2.val), YoungDiagram.mem_iff_lt_rowLen.mpr c.2.isLt⟩
  left_inv c := Subtype.ext rfl
  right_inv c := by rcases c with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; rfl

lemma card_eq_sum_rowLens (μ : YoungDiagram) : μ.card = μ.rowLens.sum := by
  classical
  have h := Fintype.card_congr (rowCellEquiv μ)
  simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_fin] at h
  change μ.card = ∑ x : Fin (μ.colLen 0), μ.rowLen x at h
  rw [h, YoungDiagram.rowLens]
  rw [← List.sum_toFinset _ List.nodup_range]
  have he : (List.range (μ.colLen 0)).toFinset = Finset.range (μ.colLen 0) := by
    ext i; simp
  rw [he]
  exact Fin.sum_univ_eq_sum_range μ.rowLen (μ.colLen 0)

/- Conversion from Mathlib's partition type to its Young diagram. -/
def partitionDiagram {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

lemma partitionDiagram_rowLens {n : ℕ} (p : Nat.Partition n) :
    (partitionDiagram p).rowLens = p.parts.sort (· ≥ ·) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro a ha
  exact p.parts_pos (by simpa only [← Multiset.mem_coe, Multiset.sort_eq] using ha)

lemma partitionDiagram_card {n : ℕ} (p : Nat.Partition n) : (partitionDiagram p).card = n := by
  rw [card_eq_sum_rowLens, partitionDiagram_rowLens, ← Multiset.sum_coe,
    Multiset.sort_eq, p.parts_sum]

lemma partitionDiagram_injective {n : ℕ} :
    Function.Injective (partitionDiagram (n := n)) := by
  intro p q h
  apply Nat.Partition.ext
  have he := congrArg (fun μ => (μ.rowLens : Multiset ℕ)) h
  simpa only [partitionDiagram_rowLens, Multiset.sort_eq] using he

def partitionTableau {n : ℕ} (p : Nat.Partition n) : Tableau n (partitionDiagram p) :=
  canonicalTableau _ (partitionDiagram_card p)

/- Cycle-type partition, with only the definitional `card (Fin n)=n` transport. -/
def permPartition {n : ℕ} (g : Equiv.Perm (Fin n)) : Nat.Partition n :=
  ⟨g.partition.parts, g.partition.parts_pos, g.partition.parts_sum.trans (Fintype.card_fin n)⟩

lemma isConj_of_permPartition_eq {n : ℕ} {g h : Equiv.Perm (Fin n)}
    (hh : permPartition g = permPartition h) : IsConj g h := by
  apply Equiv.Perm.partition_eq_of_isConj.mpr
  have hp := congrArg (fun p : Nat.Partition n => p.parts) hh
  exact Nat.Partition.ext hp

/- Class functions on the symmetric group, indexed by cycle type. -/
def classFunctions (n : ℕ) : Submodule ℂ (Equiv.Perm (Fin n) → ℂ) where
  carrier := {f | ∀ g h, permPartition g = permPartition h → f g = f h}
  zero_mem' := by
    change ∀ g h, permPartition g = permPartition h → (0 : Equiv.Perm (Fin n) → ℂ) g = 0
    intro g h hh; rfl
  add_mem' := by intro f h hf hh g k hk; simp only [Pi.add_apply, hf g k hk, hh g k hk]
  smul_mem' := by intro c f hf g k hk; simp only [Pi.smul_apply, hf g k hk]

/- Select one representative where a cycle partition is realized; unused
coordinates are zero. This gives an injection even without surjectivity of
cycle-type realization. -/
def classEvaluation (n : ℕ) : (classFunctions n) →ₗ[ℂ] (Nat.Partition n → ℂ) where
  toFun f p := if h : ∃ g : Equiv.Perm (Fin n), permPartition g = p then f.val h.choose else 0
  map_add' f h := by
    ext p
    simp only [Pi.add_apply, Submodule.coe_add]
    split_ifs <;> simp
  map_smul' c f := by
    ext p
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply]
    split_ifs <;> simp

lemma classEvaluation_injective (n : ℕ) : Function.Injective (classEvaluation n) := by
  intro f h he
  apply Subtype.ext
  funext g
  have hh := congrFun he (permPartition g)
  have hex : ∃ k : Equiv.Perm (Fin n), permPartition k = permPartition g := ⟨g, rfl⟩
  change (if hc : ∃ k : Equiv.Perm (Fin n), permPartition k = permPartition g then
    f.val hc.choose else 0) = (if hc : ∃ k : Equiv.Perm (Fin n), permPartition k = permPartition g then
    h.val hc.choose else 0) at hh
  rw [dite_eq_left hex, dite_eq_left hex] at hh
  exact (f.property _ _ hex.choose_spec).symm.trans (hh.trans (h.property _ _ hex.choose_spec))

lemma classFunctions_finrank_le (n : ℕ) :
    Module.finrank ℂ (classFunctions n) ≤ Fintype.card (Nat.Partition n) := by
  have h := LinearMap.finrank_le_finrank_of_injective (classEvaluation_injective n)
  simpa using h

lemma char_mem_classFunctions {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    ρ.character ∈ classFunctions n := by
  intro g h he
  obtain ⟨k, rfl⟩ := isConj_iff.mp (isConj_of_permPartition_eq he)
  exact (Representation.char_conj ρ g k).symm

/- Character of the actual Specht module as an actual class function. -/
def spechtCharacter {n : ℕ} (p : Nat.Partition n) : classFunctions n :=
  ⟨(spechtRep (partitionTableau p)).character, char_mem_classFunctions _⟩

/- Bilinear character scalar product used by the finite-group orthogonality theorem. -/
def charFunctional {G : Type uG} [Group G] [Fintype G] (y : G → ℂ) : (G → ℂ) →ₗ[ℂ] ℂ where
  toFun x := (Nat.card G : ℂ)⁻¹ * ∑ g, x g * y g⁻¹
  map_add' x z := by simp [Finset.sum_add_distrib, add_mul, mul_add]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc, mul_left_comm]

lemma complex_card_ne_zero (G : Type uG) [Group G] [Fintype G] : (Nat.card G : ℂ) ≠ 0 := by
  exact_mod_cast Nat.card_pos.ne'

lemma spechtCharacter_orthonormal {n : ℕ} (p q : Nat.Partition n) :
    charFunctional (spechtCharacter q).val (spechtCharacter p).val = if p = q then 1 else 0 := by
  classical
  let : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (complex_card_ne_zero _)
  let := specht_irreducible (partitionTableau p)
  let := specht_irreducible (partitionTableau q)
  have h := Representation.char_orthonormal (spechtRep (partitionTableau p))
    (spechtRep (partitionTableau q))
  change _ = _ at h
  have he : Nonempty ((spechtRep (partitionTableau q)).Equiv
      (spechtRep (partitionTableau p))) ↔ p = q := by
    constructor
    · rintro ⟨e⟩
      exact (partitionDiagram_injective
        (specht_shape_rigidity (partitionTableau q) (partitionTableau p) e)).symm
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  simpa only [he, charFunctional, spechtCharacter, LinearMap.coe_mk, AddHom.coe_mk] using h

lemma spechtCharacter_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (spechtCharacter (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have h := congrArg (fun f : classFunctions n => charFunctional (spechtCharacter p).val f.val) hc
  change charFunctional (spechtCharacter p).val
    ((classFunctions n).subtype (∑ i, c i • spechtCharacter i)) =
    charFunctional (spechtCharacter p).val ((classFunctions n).subtype 0) at h
  simp only [map_sum, map_smul, map_zero] at h
  change (∑ i, c i * charFunctional (spechtCharacter p).val (spechtCharacter i).val) = 0 at h
  simp_rw [spechtCharacter_orthonormal] at h
  simpa using h

lemma spechtCharacter_span (n : ℕ) :
    Submodule.span ℂ (Set.range (spechtCharacter (n := n))) = ⊤ := by
  apply (spechtCharacter_linearIndependent n).span_eq_top_of_card_eq_finrank'
  exact le_antisymm (spechtCharacter_linearIndependent n).fintype_card_le_finrank
    (classFunctions_finrank_le n)



theorem irreducible_equiv_specht {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    [Representation.IsIrreducible ρ] :
    ∃ p : Nat.Partition n, Nonempty (ρ.Equiv (spechtRep (partitionTableau p))) := by
  classical
  let : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (complex_card_ne_zero _)
  by_contra h
  push Not at h
  let f : (classFunctions n) →ₗ[ℂ] ℂ :=
    (charFunctional ρ.character).comp (classFunctions n).subtype
  have hf : ∀ p : Nat.Partition n, f (spechtCharacter p) = 0 := by
    intro p
    let := specht_irreducible (partitionTableau p)
    have hp := Representation.char_orthonormal (spechtRep (partitionTableau p)) ρ
    rw [ite_eq_right (fun he => (h p).false he.some)] at hp
    exact hp
  have hk : Submodule.span ℂ (Set.range (spechtCharacter (n := n))) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hf p
  rw [spechtCharacter_span] at hk
  have hz := hk (show (⟨ρ.character, char_mem_classFunctions ρ⟩ : classFunctions n) ∈ ⊤ from trivial)
  change charFunctional ρ.character ρ.character = 0 at hz
  have hone := Representation.char_orthonormal ρ ρ
  rw [ite_eq_left ⟨Representation.Equiv.refl ρ⟩] at hone
  exact one_ne_zero (hone.symm.trans hz)



lemma columnAlt_eq_zero_of_rows {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (hd : d < μ.colLen 0) : columnAlt (d := d) t = 0 := by
  classical
  have hz : ∀ a : Fin n → Fin d, columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
    intro a
    let j : Fin (μ.colLen 0) → Fin n := fun i => t.symm
      ⟨(i.val, 0), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩
    have hnot : ¬ Function.Injective (a ∘ j) := by
      intro hi
      have hh := Fintype.card_le_of_injective _ hi
      simp only [Fintype.card_fin] at hh
      omega
    simp only [Function.Injective] at hnot
    push Not at hnot
    obtain ⟨i, k, ha, hik⟩ := hnot
    have hj : j i ≠ j k := by
      intro he
      apply hik
      apply Fin.ext
      have hh := congrArg (fun l => (t l).val.1) he
      simpa [j] using hh
    exact columnAlt_collision t a (j i) (j k) hj (by simp [j]) ha
  apply LinearMap.ext
  intro x
  have he : x = ∑ a, x a • Pi.single a (1 : ℂ) := by
    ext b
    simp [Pi.single_apply]
  rw [he, map_sum]
  simp only [map_smul, hz, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

/- A Specht constituent of a `d`-letter position representation has at most
`d` rows, proved by the genuine first-column antisymmetrizer. -/
theorem specht_rows_of_hom {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep t) (wordRep n d)) (hf : f ≠ 0) :
    μ.colLen 0 ≤ d := by
  classical
  let := specht_irreducible t
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  by_contra h
  have hd : d < μ.colLen 0 := lt_of_not_ge h
  let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
  have he := columnOperator_intertwining t f p
  change f (columnOperator t (spechtRep t) p) = columnAlt t (f p) at he
  rw [columnAlt_eq_zero_of_rows t hd, LinearMap.zero_apply] at he
  have hz : columnOperator t (spechtRep t) p = 0 := hi (he.trans (map_zero f).symm)
  exact columnAlt_polytabloid_ne_zero t
    ((columnOperator_subtype t (spechtSub t) p).symm.trans (congrArg Subtype.val hz))

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl
open scoped MonoidAlgebra

/- In a semisimple module, support containment is equivalent to separation
by homomorphisms (multiplicities are immaterial for the band step). -/
theorem hom_separates_of_simple_support {R : Type uR} {X : Type uX} {Y : Type uY} [Ring R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [IsSemisimpleModule R X]
    (h : ∀ S : Submodule R X, IsSimpleModule R S →
      ∃ f : S →ₗ[R] Y, f ≠ 0) (x : X) (hx : x ≠ 0) :
    ∃ f : X →ₗ[R] Y, f x ≠ 0 := by
  classical
  let K : Submodule R X := ⨅ f : X →ₗ[R] Y, LinearMap.ker f
  have hK : K = ⊥ := by
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le K with hk | ⟨S, hS, hs⟩
    · exact hk
    obtain ⟨f, hf⟩ := h S hs
    obtain ⟨F, hF⟩ := IsSemisimpleModule.extension_property S.subtype S.subtype_injective f
    exfalso
    apply hf
    ext s
    have hm : s.val ∈ K := hS s.property
    have he : F s.val = 0 := ((Submodule.mem_iInf _).mp hm F)
    change f s = 0
    exact (LinearMap.congr_fun hF s).symm.trans he
  by_contra hf
  push Not at hf
  apply hx
  have hm : x ∈ K := (Submodule.mem_iInf _).mpr (fun f => hf f)
  simpa only [hK, Submodule.mem_bot] using hm

end Saxl

namespace Saxl
open scoped MonoidAlgebra

/- The invariant-subspace and group-algebra subtype constructions agree. -/
def subrepModuleEquiv {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    S.toRepresentation.asModule ≃ₗ[ℂ[G]] S.asSubmodule where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change (⟨(a • x).val, _⟩ : S.asSubmodule) = a • ⟨x.val, x.property⟩
    apply Subtype.ext
    change (a • x).val = ρ.asModuleEquiv (a • ρ.asModuleEquiv.symm x.val)
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp only [zero_smul, map_zero]; rfl
    | add a b ha hb =>
      simp only [add_smul, map_add]
      change (a • x).val + (b • x).val = _
      rw [ha, hb]
    | single g c =>
      rw [Representation.single_smul, Representation.single_smul]
      rfl

lemma subrep_irreducible_of_simple {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Submodule ℂ[G] ρ.asModule)
    [IsSimpleModule ℂ[G] S] :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' S).toRepresentation := by
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  let e : (Subrepresentation.ofSubmodule' S).toRepresentation.asModule ≃ₗ[ℂ[G]] S :=
    subrepModuleEquiv (Subrepresentation.ofSubmodule' S)
  exact IsSimpleModule.congr e

end Saxl

namespace Saxl
open scoped MonoidAlgebra

theorem intertwining_separates_of_simple_support {G : Type uG} {X : Type uX} {Y : Type uY}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y)
    (h : ∀ S : Subrepresentation ρ, Representation.IsIrreducible S.toRepresentation →
      ∃ f : Representation.IntertwiningMap S.toRepresentation σ, f ≠ 0)
    (x : X) (hx : x ≠ 0) :
    ∃ f : Representation.IntertwiningMap ρ σ, f x ≠ 0 := by
  classical
  have hs (S : Submodule ℂ[G] ρ.asModule) (hS : IsSimpleModule ℂ[G] S) :
      ∃ f : S →ₗ[ℂ[G]] σ.asModule, f ≠ 0 := by
    let P := Subrepresentation.ofSubmodule' S
    let := hS
    obtain ⟨f, hf⟩ := h P (subrep_irreducible_of_simple S)
    let F := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
    let E : P.toRepresentation.asModule ≃ₗ[ℂ[G]] S := subrepModuleEquiv P
    refine ⟨F.comp E.symm.toLinearMap, ?_⟩
    intro hz
    apply hf
    apply (Representation.IntertwiningMap.equivLinearMapAsModule _ _).injective
    ext v
    have he := LinearMap.congr_fun hz (E v)
    change F v = 0
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      E.symm_apply_apply, LinearMap.zero_apply] using he
  obtain ⟨f, hf⟩ := hom_separates_of_simple_support hs (ρ.asModuleEquiv.symm x)
    (fun he => hx (ρ.asModuleEquiv.symm.injective (he.trans (map_zero _).symm)))
  exact ⟨(Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm f, hf⟩

end Saxl

namespace Saxl
open scoped MonoidAlgebra

end Saxl

namespace Saxl

def subrepInclusion {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    Representation.IntertwiningMap S.toRepresentation ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

/- All constituents needed from a d-letter permutation module are detected
by a module containing each Specht type of height at most d. -/
theorem word_support_separates {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (h : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ d →
      ∃ f : Representation.IntertwiningMap (spechtRep t) σ, f ≠ 0)
    (x : WordSpace n d) (hx : x ≠ 0) :
    ∃ f : Representation.IntertwiningMap (wordRep n d) σ, f x ≠ 0 := by
  apply intertwining_separates_of_simple_support (wordRep n d) σ ?_ x hx
  intro S hS
  let := hS
  obtain ⟨p, ⟨e⟩⟩ := irreducible_equiv_specht S.toRepresentation
  let t := partitionTableau p
  let i : Representation.IntertwiningMap (spechtRep t) (wordRep n d) :=
    (subrepInclusion S).comp e.symm.toIntertwiningMap
  have hi : i ≠ 0 := by
    intro he
    have hz := congrArg (fun F : Representation.IntertwiningMap (spechtRep t) (wordRep n d) =>
      F ⟨polytabloid t, mem_cyclic _ _⟩) he
    have h0 : e.symm ⟨polytabloid t, mem_cyclic _ _⟩ = 0 := Subtype.ext hz
    have h1 := e.symm.injective (h0.trans (map_zero _).symm)
    exact polytabloid_ne_zero t (congrArg Subtype.val h1)
  obtain ⟨f, hf⟩ := h _ t (specht_rows_of_hom t i hi)
  refine ⟨f.comp e.toIntertwiningMap, ?_⟩
  intro he
  apply hf
  ext y
  obtain ⟨z, rfl⟩ := e.surjective y
  exact congrArg (fun F : Representation.IntertwiningMap S.toRepresentation σ => F z) he

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Concatenation of words on independent position blocks. -/
def joinPositions {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : Fin a → Fin d) (y : Fin b → Fin d) : Fin n → Fin d :=
  fun i => Sum.elim x y (e i)

@[simp] lemma leftWord_join {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : Fin a → Fin d) (y : Fin b → Fin d) : leftWord e (joinPositions e x y) = x := by
  funext i
  simp [leftWord, joinPositions]

@[simp] lemma rightWord_join {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : Fin a → Fin d) (y : Fin b → Fin d) : rightWord e (joinPositions e x y) = y := by
  funext i
  simp [rightWord, joinPositions]

@[simp] lemma joinPositions_parts {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w : Fin n → Fin d) : joinPositions e (leftWord e w) (rightWord e w) = w := by
  funext i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j <;> simp [joinPositions,leftWord,rightWord]

def positionUncurry {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    ((Fin b → Fin d) → WordSpace a d) ≃ₗ[ℂ] WordSpace n d where
  toFun f w := f (rightWord e w) (leftWord e w)
  invFun z y x := z (joinPositions e x y)
  left_inv f := by ext y x; simp
  right_inv z := by ext w; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def positionTensor {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    WordSpace a d ⊗[ℂ] WordSpace b d ≃ₗ[ℂ] WordSpace n d :=
  TensorProduct.piScalarRight ℂ ℂ (WordSpace a d) (Fin b → Fin d) ≪≫ₗ positionUncurry e

@[simp] lemma positionTensor_tmul {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : WordSpace a d) (y : WordSpace b d) :
    positionTensor e (x ⊗ₜ[ℂ] y) = positionProduct e x y := by
  funext w
  change y (rightWord e w) * x (leftWord e w) = _
  exact mul_comm _ _

lemma positionProduct_equivariant {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b))
    (x : WordSpace a d) (y : WordSpace b d) :
    wordRep n d (sumPerm e g h) (positionProduct e x y) =
      positionProduct e (wordRep a d g x) (wordRep b d h y) := by
  funext w
  change x (leftWord e (w ∘ sumPerm e g h)) * y (rightWord e (w ∘ sumPerm e g h)) = _
  have hl : leftWord e (w ∘ sumPerm e g h) = leftWord e w ∘ g := by
    funext i
    simp [leftWord]
  have hr : rightWord e (w ∘ sumPerm e g h) = rightWord e w ∘ h := by
    funext i
    simp [rightWord]
  rw [hl,hr]
  rfl

lemma positionTensor_equivariant {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b))
    (z : WordSpace a d ⊗[ℂ] WordSpace b d) :
    positionTensor e (TensorProduct.map (wordRep a d g) (wordRep b d h) z) =
      wordRep n d (sumPerm e g h) (positionTensor e z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => rw [TensorProduct.map_tmul, positionTensor_tmul, positionTensor_tmul, positionProduct_equivariant]

lemma product_mem_cyclic {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (u : WordSpace b d)
    (x : WordSpace a d) (y : WordSpace b d)
    (hx : x ∈ cyclic (wordRep a d) v) (hy : y ∈ cyclic (wordRep b d) u) :
    positionProduct e x y ∈ cyclic (wordRep n d) (positionProduct e v u) := by
  let S := cyclic (wordRep n d) (positionProduct e v u)
  change x ∈ Submodule.span ℂ _ at hx
  change y ∈ Submodule.span ℂ _ at hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h,rfl⟩ := hy
      rw [← positionProduct_equivariant]
      exact S.apply_mem_toSubmodule (sumPerm e g h) (mem_cyclic _ _)
    | zero =>
      have hz : positionProduct e (wordRep a d g v) 0 = 0 := by ext; simp [positionProduct]
      rw [hz]
      exact S.toSubmodule.zero_mem
    | add y z hy hz ihy ihz =>
      have he : positionProduct e (wordRep a d g v) (y+z) =
          positionProduct e (wordRep a d g v) y + positionProduct e (wordRep a d g v) z := by
        ext; simp [positionProduct,mul_add]
      rw [he]
      exact S.toSubmodule.add_mem ihy ihz
    | smul c y hy ih =>
      have he : positionProduct e (wordRep a d g v) (c • y) =
          c • positionProduct e (wordRep a d g v) y := by ext; simp [positionProduct,mul_left_comm]
      rw [he]
      exact S.toSubmodule.smul_mem c ih
  | zero =>
    have hz : positionProduct e 0 y = 0 := by ext; simp [positionProduct]
    rw [hz]
    exact S.toSubmodule.zero_mem
  | add x z hx hz ihx ihz =>
    have he : positionProduct e (x+z) y = positionProduct e x y + positionProduct e z y := by
      ext; simp [positionProduct,add_mul]
    rw [he]
    exact S.toSubmodule.add_mem ihx ihz
  | smul c x hx ih =>
    have he : positionProduct e (c • x) y = c • positionProduct e x y := by
      ext; simp [positionProduct,mul_assoc]
    rw [he]
    exact S.toSubmodule.smul_mem c ih

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

@[simp] lemma sumPerm_mul {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g g' : Equiv.Perm (Fin a)) (h h' : Equiv.Perm (Fin b)) :
    sumPerm e (g*g') (h*h') = sumPerm e g h * sumPerm e g' h' := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j <;> simp only [sumPerm_left, sumPerm_right, Equiv.Perm.mul_apply]

@[simp] lemma sumPerm_one {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    sumPerm e 1 1 = 1 := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j <;> simp only [sumPerm_left,sumPerm_right,Equiv.Perm.one_apply]

lemma sumPerm_inv {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
    sumPerm e g⁻¹ h⁻¹ = (sumPerm e g h)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_left
  rw [← sumPerm_mul, inv_mul_cancel, inv_mul_cancel, sumPerm_one]

def bandOrbitMap {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y) :
    X →ₗ[ℂ] ((Fin b → Fin k) → Y) where
  toFun x w := ∑ g : Equiv.Perm (Fin b),
    ((Pi.single (c ∘ (g⁻¹ : Equiv.Perm (Fin b))) (1:ℂ) : WordSpace b k) w) • F (ρ (sumPerm e 1 g⁻¹) x)
  map_add' x y := by ext w; simp only [map_add,smul_add,Finset.sum_add_distrib,Pi.add_apply]
  map_smul' c x := by
    ext w
    simp only [map_smul,Pi.smul_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    exact smul_comm _ _ _

lemma bandOrbitMap_base {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y)
    (hF : ∀ g : Equiv.Perm (Fin b), c ∘ g = c → ∀ x, F (ρ (sumPerm e 1 g) x) = F x)
    (x : X) : bandOrbitMap e ρ c F x c =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin b) => c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c)).card : ℂ) • F x := by
  classical
  change (∑ g : Equiv.Perm (Fin b), _) = _
  have hh (g : Equiv.Perm (Fin b)) :
      ((Pi.single (c ∘ (g⁻¹ : Equiv.Perm (Fin b))) (1:ℂ) : WordSpace b k) c) • F (ρ (sumPerm e 1 g⁻¹) x) =
      if c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c then F x else 0 := by
    by_cases h : c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c
    · rw [ite_eq_left h, h, Pi.single_eq_same, one_smul, hF g⁻¹ h]
    · rw [ite_eq_right h, Pi.single_eq_of_ne (Ne.symm h), zero_smul]
  simp only [hh]
  simp [Finset.sum_ite,Nat.cast_smul_eq_nsmul]

lemma bandOrbitMap_nonzero {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y) (hF0 : F ≠ 0)
    (hF : ∀ g : Equiv.Perm (Fin b), c ∘ g = c → ∀ x, F (ρ (sumPerm e 1 g) x) = F x) :
    bandOrbitMap e ρ c F ≠ 0 := by
  classical
  intro hz
  apply hF0
  ext x
  have hh := bandOrbitMap_base e ρ c F hF x
  rw [hz] at hh
  change 0 = _ at hh
  have hc : ((Finset.univ.filter (fun g : Equiv.Perm (Fin b) =>
      c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c)).card : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact Finset.card_ne_zero.mpr ⟨1,Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  exact (smul_eq_zero.mp hh.symm).resolve_left hc

lemma bandOrbitMap_equivariant {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (τ : Representation ℂ (Equiv.Perm (Fin a)) Y)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y)
    (hF : ∀ h : Equiv.Perm (Fin a), ∀ x, F (ρ (sumPerm e h 1) x) = τ h (F x))
    (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) (x : X) (w : Fin b → Fin k) :
    bandOrbitMap e ρ c F (ρ (sumPerm e h q) x) w =
      τ h (bandOrbitMap e ρ c F x (w ∘ q)) := by
  classical
  change (∑ g : Equiv.Perm (Fin b), _) = τ h (∑ g : Equiv.Perm (Fin b), _)
  rw [map_sum]
  apply (Equiv.sum_comp (Equiv.mulLeft q) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  have he : sumPerm e 1 (q*g)⁻¹ * sumPerm e h q = sumPerm e h 1 * sumPerm e 1 g⁻¹ := by
    rw [← sumPerm_mul, ← sumPerm_mul]
    simp only [one_mul,mul_one,mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one]
  change _ • F (ρ (sumPerm e 1 (q*g)⁻¹) (ρ (sumPerm e h q) x)) = _
  rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hF, map_smul]
  congr 1
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro hh
    funext i
    have hi := congrFun hh (q i)
    simpa using hi
  · intro hh
    funext i
    have hi := congrFun hh (q⁻¹ i)
    simpa using hi

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

/- Apply a band intertwiner to every scalar high-coordinate of a colored
strip orbit map. This is the concrete tensor product of the two maps. -/
def bandGlue {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d) : X →ₗ[ℂ] WordSpace n d where
  toFun x w := L (fun cb => T x cb (leftWord e w)) (rightWord e w)
  map_add' x y := by
    ext w
    simp only [map_add, Pi.add_apply]
    change L ((fun cb => T x cb (leftWord e w)) + (fun cb => T y cb (leftWord e w))) (rightWord e w) = _
    rw [map_add]
    rfl
  map_smul' c x := by
    ext w
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    change L (c • (fun cb => T x cb (leftWord e w))) (rightWord e w) = _
    rw [map_smul]
    rfl

lemma bandGlue_sum {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d) (x : X) :
    bandGlue e T L x = ∑ c : Fin b → Fin k, positionProduct e (T x c) (L (Pi.single c 1)) := by
  classical
  ext w
  change L (fun cb => T x cb (leftWord e w)) (rightWord e w) = _
  have he : (fun cb => T x cb (leftWord e w)) =
      ∑ c : Fin b → Fin k, T x c (leftWord e w) • (Pi.single c (1:ℂ) : WordSpace b k) := by
    ext c
    simp [Pi.single_apply]
  rw [he, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, positionProduct]

lemma bandGlue_equivariant {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (hT : ∀ h q x w, T (ρ (sumPerm e h q) x) w = wordRep a d h (T x (w ∘ q)))
    (L : Representation.IntertwiningMap (wordRep b k) (wordRep b d))
    (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) (x : X) :
    bandGlue e T L.toLinearMap (ρ (sumPerm e h q) x) =
      wordRep n d (sumPerm e h q) (bandGlue e T L.toLinearMap x) := by
  ext w
  change L (fun cb => T (ρ (sumPerm e h q) x) cb (leftWord e w)) (rightWord e w) = _
  simp only [hT]
  have he : (fun cb => (wordRep a d h (T x (cb ∘ q))) (leftWord e w)) =
      wordRep b k q (fun cb => T x cb ((leftWord e w) ∘ h)) := rfl
  rw [he]
  have hL : L (wordRep b k q (fun cb => T x cb ((leftWord e w) ∘ h))) =
      wordRep b d q (L (fun cb => T x cb ((leftWord e w) ∘ h))) :=
    LinearMap.congr_fun (L.isIntertwining' q) _
  rw [hL]
  change L (fun cb => T x cb ((leftWord e w) ∘ h)) ((rightWord e w) ∘ q) =
    L (fun cb => T x cb (leftWord e (w ∘ sumPerm e h q))) (rightWord e (w ∘ sumPerm e h q))
  have hl : leftWord e (w ∘ sumPerm e h q) = (leftWord e w) ∘ h := by
    funext i
    simp [leftWord,sumPerm_left]
  have hr : rightWord e (w ∘ sumPerm e h q) = (rightWord e w) ∘ q := by
    funext i
    simp [rightWord,sumPerm_right]
  rw [hl,hr]

lemma bandGlue_mem {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (hT : ∀ x c, T x c ∈ cyclic (wordRep a d) v)
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d)
    (hL : ∀ y, L y ∈ cyclic (wordRep b d) u) (x : X) :
    bandGlue e T L x ∈ cyclic (wordRep n d) (positionProduct e v u) := by
  rw [bandGlue_sum]
  apply Submodule.sum_mem
  intro c hc
  exact product_mem_cyclic e v u _ _ (hT x c) (hL _)

/- A module containing every band Specht type of the relevant height detects
any nonzero high-valued colored-band vector. No multiplicity hypothesis is needed. -/
theorem bandGlue_exists {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (v : WordSpace a d) (u : WordSpace b d)
    (hband : ∀ (μ : YoungDiagram) (t : Tableau b μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t) (cyclic (wordRep b d) u).toRepresentation, f ≠ 0)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d)) (hT0 : T ≠ 0)
    (hT : ∀ h q x w, T (ρ (sumPerm e h q) x) w = wordRep a d h (T x (w ∘ q)))
    (hTm : ∀ x c, T x c ∈ cyclic (wordRep a d) v) :
    ∃ f : X →ₗ[ℂ] WordSpace n d, f ≠ 0 ∧
      (∀ h q x, f (ρ (sumPerm e h q) x) = wordRep n d (sumPerm e h q) (f x)) ∧
      (∀ x, f x ∈ cyclic (wordRep n d) (positionProduct e v u)) := by
  classical
  obtain ⟨x,c,w,hxc⟩ : ∃ x c w, T x c w ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hT0
    ext x c w
    exact hh x c w
  have hv : (fun cb => T x cb w) ≠ (0 : WordSpace b k) := by
    intro hz
    exact hxc (congrFun hz c)
  obtain ⟨L,hL⟩ := word_support_separates (cyclic (wordRep b d) u).toRepresentation hband _ hv
  let L' := (subrepInclusion (cyclic (wordRep b d) u)).comp L
  have hL' : L' (fun cb => T x cb w) ≠ 0 := by
    intro hz
    apply hL
    exact Subtype.ext hz
  obtain ⟨z,hz⟩ : ∃ z, L' (fun cb => T x cb w) z ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hL' (funext hh)
  refine ⟨bandGlue e T L'.toLinearMap, ?_, bandGlue_equivariant e ρ T hT L', ?_⟩
  · intro he
    apply hz
    have hh := congrArg (fun f : X →ₗ[ℂ] WordSpace n d => f x (joinPositions e w z)) he
    change L' (fun cb => T x cb (leftWord e (joinPositions e w z))) (rightWord e (joinPositions e w z)) = 0 at hh
    simpa only [leftWord_join, rightWord_join] using hh
  · exact bandGlue_mem e v u T hTm L'.toLinearMap (fun y => (L y).property)


def coordinateSub (n d : ℕ) (P : (Fin n → Fin d) → Prop) : Submodule ℂ (WordSpace n d) where
  carrier := {x | ∀ w, ¬ P w → x w = 0}
  zero_mem' := by intro w hw; rfl
  add_mem' := by intro x y hx hy w hw; change x w+y w=0; rw [hx w hw,hy w hw,add_zero]
  smul_mem' := by intro c x hx w hw; change c*x w=0; rw [hx w hw,mul_zero]

lemma positionProduct_sector {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (A : Fin d → Prop) (x : WordSpace a d) (y : WordSpace b d)
    (hx : x ∈ alphabetSub a d A) (hy : y ∈ alphabetSub b d (fun z => ¬A z)) :
    positionProduct e x y ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A) := by
  intro w hw
  by_contra hn
  apply hw
  have hxy : x (leftWord e w) ≠ 0 ∧ y (rightWord e w) ≠ 0 := mul_ne_zero_iff.mp hn
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j =>
    simpa only [Equiv.apply_symm_apply, Sum.isLeft_inl, iff_true,leftWord] using
      (alphabetSub_iff A x).mp hx _ hxy.1 j
  | inr j =>
    simpa only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, iff_false,rightWord] using
      (alphabetSub_iff (fun z => ¬A z) y).mp hy _ hxy.2 j

lemma bandGlue_sector {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (A : Fin d → Prop)
    (v : WordSpace a d) (u : WordSpace b d)
    (hv : v ∈ alphabetSub a d A) (hu : u ∈ alphabetSub b d (fun z => ¬A z))
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (hT : ∀ x c, T x c ∈ cyclic (wordRep a d) v)
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d)
    (hL : ∀ y, L y ∈ cyclic (wordRep b d) u) (x : X) :
    bandGlue e T L x ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A) := by
  rw [bandGlue_sum]
  apply Submodule.sum_mem
  intro c hc
  apply positionProduct_sector
  · exact cyclic_alphabet A v hv _ (hT x c)
  · exact cyclic_alphabet (fun z => ¬A z) u hu _ (hL _)

theorem bandGlue_sector_exists {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hvA : v ∈ alphabetSub a d A)
    (huA : u ∈ alphabetSub b d (fun z => ¬A z))
    (hband : ∀ (μ : YoungDiagram) (t : Tableau b μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t) (cyclic (wordRep b d) u).toRepresentation, f ≠ 0)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d)) (hT0 : T ≠ 0)
    (hT : ∀ h q x w, T (ρ (sumPerm e h q) x) w = wordRep a d h (T x (w ∘ q)))
    (hTm : ∀ x c, T x c ∈ cyclic (wordRep a d) v) :
    ∃ f : X →ₗ[ℂ] WordSpace n d, f ≠ 0 ∧
      (∀ h q x, f (ρ (sumPerm e h q) x) = wordRep n d (sumPerm e h q) (f x)) ∧
      (∀ x, f x ∈ cyclic (wordRep n d) (positionProduct e v u)) ∧
      (∀ x, f x ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A)) := by
  classical
  obtain ⟨x,c,w,hxc⟩ : ∃ x c w, T x c w ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hT0
    ext x c w
    exact hh x c w
  have hv : (fun cb => T x cb w) ≠ (0 : WordSpace b k) := by
    intro hz
    exact hxc (congrFun hz c)
  obtain ⟨L,hL⟩ := word_support_separates (cyclic (wordRep b d) u).toRepresentation hband _ hv
  let L' := (subrepInclusion (cyclic (wordRep b d) u)).comp L
  have hL' : L' (fun cb => T x cb w) ≠ 0 := by
    intro hz
    apply hL
    exact Subtype.ext hz
  obtain ⟨z,hz⟩ : ∃ z, L' (fun cb => T x cb w) z ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hL' (funext hh)
  refine ⟨bandGlue e T L'.toLinearMap, ?_, bandGlue_equivariant e ρ T hT L', ?_, ?_⟩
  · intro he
    apply hz
    have hh := congrArg (fun f : X →ₗ[ℂ] WordSpace n d => f x (joinPositions e w z)) he
    change L' (fun cb => T x cb (leftWord e (joinPositions e w z))) (rightWord e (joinPositions e w z)) = 0 at hh
    simpa only [leftWord_join, rightWord_join] using hh
  · exact bandGlue_mem e v u T hTm L'.toLinearMap (fun y => (L y).property)

  · exact bandGlue_sector e A v u hvA huA T hTm L'.toLinearMap (fun y => (L y).property)

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

def transposeTableau {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Tableau n μ.transpose := t.trans
  { toFun := fun c => ⟨c.val.swap, YoungDiagram.mem_transpose.mpr (by simp)⟩
    invFun := fun c => ⟨c.val.swap, YoungDiagram.mem_transpose.mp c.property⟩
    left_inv := by intro c; apply Subtype.ext; exact Prod.swap_swap _
    right_inv := by intro c; apply Subtype.ext; exact Prod.swap_swap _ }

/- Twisting by the actual sign character, on the same complex vector space. -/
def signTwist {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    Representation ℂ (Equiv.Perm (Fin n)) V where
  toFun g := signC g • ρ g
  map_one' := by simp
  map_mul' g h := by ext x; simp [map_mul, smul_smul, mul_comm]

lemma signTwist_irreducible {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible (signTwist ρ) := by
  let cv : Subrepresentation (signTwist ρ) ≃o Subrepresentation ρ :=
    { toFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := by
            intro g x hx
            have h := S.toSubmodule.smul_mem (signC g) (S.apply_mem_toSubmodule g hx)
            change signC g • (signC g • (ρ g x)) ∈ S.toSubmodule at h
            simpa only [smul_smul, signC_mul_self, one_smul] using h }
      invFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := by
            intro g x hx
            exact S.toSubmodule.smul_mem (signC g) (S.apply_mem_toSubmodule g hx) }
      left_inv := by intro S; rfl
      right_inv := by intro S; rfl
      map_rel_iff' := by intros; rfl }
  exact cv.isSimpleOrder_iff.mpr inferInstance

def orbitAverage {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (a : Fin n → Fin d) (y : V) :
    Representation.IntertwiningMap (wordRep n d) ρ where
  toFun x := ∑ g : Equiv.Perm (Fin n), x (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ g y
  map_add' x z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [smul_smul, Finset.smul_sum]
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    change (∑ g : Equiv.Perm (Fin n), x ((a ∘ (g⁻¹ : Equiv.Perm (Fin n))) ∘ h) • ρ g y) =
      ρ h (∑ g : Equiv.Perm (Fin n), x (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ g y)
    simp only [map_sum, map_smul]
    apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
    apply Finset.sum_congr rfl
    intro g hg
    change x ((a ∘ ((h * g)⁻¹ : Equiv.Perm (Fin n))) ∘ h) • ρ (h * g) y =
      x (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ h (ρ g y)
    simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
    congr 2
    funext i
    simp

lemma orbitAverage_base {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (a : Fin n → Fin d) (y : V)
    (hy : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ρ g y = y) :
    orbitAverage ρ a y (Pi.single a 1) =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin n) => a ∘ g = a)).card : ℂ) • y := by
  classical
  change (∑ g : Equiv.Perm (Fin n), (Pi.single a (1 : ℂ) : WordSpace n d) (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ g y) = _
  have hi (g : Equiv.Perm (Fin n)) : a ∘ (g⁻¹ : Equiv.Perm (Fin n)) = a ↔ a ∘ g = a := by
    constructor <;> intro hh <;> funext i
    · have he := congrFun hh (g i); simpa using he.symm
    · have he := congrFun hh (g⁻¹ i); simpa using he.symm
  simp only [Pi.single_apply, hi]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_congr rfl (fun g hg => hy g (Finset.mem_filter.mp hg).2)]
  simp [Nat.cast_smul_eq_nsmul]

end Saxl

namespace Saxl
/- Sign-conjugacy proved using the column-antisymmetrized row tabloids. -/
theorem specht_sign_transpose {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Nonempty ((spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) := by
  classical
  let tt := transposeTableau t
  let y : Specht tt := ⟨polytabloid tt, mem_cyclic _ _⟩
  let R := signTwist (spechtRep tt)
  let F := orbitAverage R (rowWord t) y
  let c : ℂ := ((Finset.univ.filter
    (fun g : Equiv.Perm (Fin n) => rowWord t ∘ g = rowWord t)).card : ℂ)
  have hy : ∀ g : Equiv.Perm (Fin n), rowWord t ∘ g = rowWord t → R g y = y := by
    intro g hg
    have hc : g ∈ columnGroup tt := by
      intro i
      exact congrArg Fin.val (congrFun hg i)
    apply Subtype.ext
    change signC g • wordRep n (μ.transpose.colLen 0) g (polytabloid tt) = polytabloid tt
    rw [polytabloid_alternating tt ⟨g, hc⟩, smul_smul, signC_mul_self, one_smul]
  have hF : F (Pi.single (rowWord t) 1) = c • y := orbitAverage_base R _ y hy
  have hc0 : c ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply Finset.card_ne_zero.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rfl
  have hm (g : columnGroup t) :
      (F (wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n))
        (Pi.single (rowWord t) 1))).val (rowWord tt) = signC (g : Equiv.Perm (Fin n)) * c := by
    rw [F.isIntertwining, hF]
    change signC (g : Equiv.Perm (Fin n)) * (c *
      polytabloid tt (rowWord tt ∘ (g : Equiv.Perm (Fin n)))) = _
    have he : rowWord tt ∘ (g : Equiv.Perm (Fin n)) = rowWord tt := by
      funext i
      apply Fin.ext
      exact g.property i
    rw [he, polytabloid_rowWord, mul_one]
  let inc : Representation.IntertwiningMap (spechtRep t) (wordRep n (μ.colLen 0)) :=
    { toLinearMap := (spechtSub t).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let f := F.comp inc
  have hf : f ≠ 0 := by
    intro hz
    have he : (F (polytabloid t)).val (rowWord tt) = 0 := by
      have he := congrArg (fun l : Representation.IntertwiningMap (spechtRep t) R =>
        (l ⟨polytabloid t, mem_cyclic _ _⟩).val (rowWord tt)) hz
      exact he
    let := Fintype.ofFinite (columnGroup t)
    have hp : (F (polytabloid t)).val (rowWord tt) =
        (Fintype.card (columnGroup t) : ℂ) * c := by
      change (F (∑ g : columnGroup t, signC (g : Equiv.Perm (Fin n)) •
        wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1))).val _ = _
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm]
      simp only [← mul_assoc, signC_mul_self, one_mul, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card (columnGroup t) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (mul_ne_zero hn hc0) (hp.symm.trans he)
  let := specht_irreducible t
  let := specht_irreducible tt
  let := signTwist_irreducible (spechtRep tt)
  exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩
end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A horizontal strip removes at most one cell in each column. -/
def HorizontalStrip (ν μ : YoungDiagram) : Prop :=
  ν ≤ μ ∧ ∀ x ∈ μ, x ∉ ν → ∀ y ∈ μ, y ∉ ν → x.2 = y.2 → x = y

/- Position embedding induced by inclusion of the actual Young diagrams. -/
def tableauInclusion {a n : ℕ} {ν μ : YoungDiagram} (s : Tableau a ν) (t : Tableau n μ)
    (h : ν ≤ μ) : Fin a ↪ Fin n where
  toFun i := t.symm ⟨(s i).val, h (s i).property⟩
  inj' := by
    intro i j hij
    apply s.injective
    apply Subtype.ext
    simpa using congrArg (fun k => (t k).val) hij

lemma colLen_mono {ν μ : YoungDiagram} (h : ν ≤ μ) (j : ℕ) :
    ν.colLen j ≤ μ.colLen j := by
  by_contra hn
  have hm : (μ.colLen j, j) ∈ ν := YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_not_ge hn)
  exact (lt_irrefl _) (YoungDiagram.mem_iff_lt_colLen.mp (h hm))

def rowLetterInclusion {ν μ : YoungDiagram} (h : ν ≤ μ) : Fin (ν.colLen 0) ↪ Fin (μ.colLen 0) :=
  Fin.castLEEmb (colLen_mono h 0)

/- Restrict letters on a specified position set, and sum over all other letters.
This is precisely contraction with the all-ones functional at deleted positions. -/
def wordRestrict {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e) :
    WordSpace n e →ₗ[ℂ] WordSpace a d where
  toFun x b := ∑ c : Fin n → Fin e, if c ∘ i = j ∘ b then x c else 0
  map_add' x y := by
    ext b
    change (∑ c, if c ∘ i = j ∘ b then x c + y c else 0) =
      (∑ c, if c ∘ i = j ∘ b then x c else 0) + (∑ c, if c ∘ i = j ∘ b then y c else 0)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    split <;> simp_all
  map_smul' r x := by
    ext b
    change (∑ c, if c ∘ i = j ∘ b then r * x c else 0) =
      r * ∑ c, if c ∘ i = j ∘ b then x c else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    split <;> simp_all

lemma wordRestrict_single {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (c : Fin n → Fin e) (b : Fin a → Fin d) :
    wordRestrict i j (Pi.single c 1) b = if c ∘ i = j ∘ b then 1 else 0 := by
  classical
  change (∑ z : Fin n → Fin e, if z ∘ i = j ∘ b then (Pi.single c (1 : ℂ) : WordSpace n e) z else 0) = _
  rw [Finset.sum_eq_single c]
  · simp
  · intro z hz hzc
    simp [hzc]
  · simp

lemma wordRestrict_equivariant {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)) (hi : ∀ k, g (i k) = i (h k))
    (x : WordSpace n e) :
    wordRestrict i j (wordRep n e g x) = wordRep a d h (wordRestrict i j x) := by
  classical
  ext b
  change (∑ c : Fin n → Fin e, if c ∘ i = j ∘ b then x (c ∘ g) else 0) =
    ∑ c : Fin n → Fin e, if c ∘ i = j ∘ (b ∘ h) then x c else 0
  apply Eq.trans ?_ (Equiv.sum_comp (wordPerm n e g)
    (fun c => if c ∘ i = j ∘ (b ∘ h) then x c else 0))
  apply Finset.sum_congr rfl
  intro c hc
  change (if c ∘ i = j ∘ b then x (c ∘ g) else 0) =
    if (c ∘ g) ∘ i = j ∘ (b ∘ h) then x (c ∘ g) else 0
  congr 1
  apply propext
  constructor
  · intro hh
    funext k
    simpa only [Function.comp_apply, hi] using congrFun hh (h k)
  · intro hh
    funext k
    have he := congrFun hh (h⁻¹ k)
    simpa [Function.comp_apply, hi] using he


@[simp] lemma tableauInclusion_cell {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (h : ν ≤ μ) (k : Fin a) :
    (t (tableauInclusion s t h k)).val = (s k).val := by
  change (t (t.symm ⟨(s k).val, h (s k).property⟩)).val = _
  simp

lemma column_fixed_of_strip {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ)
    (g : columnGroup t) (hg : ∀ i, (g : Equiv.Perm (Fin n)) (tableauInclusion s t hs.1 i) =
      tableauInclusion s t hs.1 i) : g = 1 := by
  have hin (k : Fin n) (hk : (t k).val ∈ ν) : (g : Equiv.Perm (Fin n)) k = k := by
    let i := s.symm ⟨(t k).val, hk⟩
    have he : tableauInclusion s t hs.1 i = k := by
      apply t.injective
      apply Subtype.ext
      rw [tableauInclusion_cell]
      simp [i]
    simpa only [he] using hg i
  apply Subtype.ext
  apply Equiv.ext
  intro k
  by_cases hk : (t k).val ∈ ν
  · exact hin k hk
  · have ho : (t ((g : Equiv.Perm (Fin n)) k)).val ∉ ν := by
      intro hh
      have he := hin ((g : Equiv.Perm (Fin n)) k) hh
      have he' := (g : Equiv.Perm (Fin n)).injective he
      exact hk (he' ▸ hh)
    apply t.injective
    apply Subtype.ext
    exact hs.2 _ (t _).property ho _ (t _).property hk (g.property k)

lemma strip_contraction_coefficient {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
      (polytabloid t) (rowWord s) = 1 := by
  classical
  let i := tableauInclusion s t hs.1
  let j := rowLetterInclusion hs.1
  have he (g : columnGroup t) :
      (rowWord t ∘ ((g : Equiv.Perm (Fin n))⁻¹ : Equiv.Perm (Fin n))) ∘ i = j ∘ rowWord s ↔ g = 1 := by
    constructor
    · intro hh
      have hf : ∀ k, ((g : Equiv.Perm (Fin n))⁻¹) (i k) = i k := by
        intro k
        apply t.injective
        apply Subtype.ext
        apply Prod.ext
        · have hh' := congrArg Fin.val (congrFun hh k)
          simpa [rowWord, j, rowLetterInclusion, i] using hh'
        · exact (g⁻¹).property (i k)
      have hh' : (g⁻¹ : columnGroup t) = 1 := column_fixed_of_strip s t hs (g⁻¹) hf
      simpa using congrArg Inv.inv hh'
    · rintro rfl
      funext k
      apply Fin.ext
      exact congrArg Prod.fst (tableauInclusion_cell s t hs.1 k)
  let := Fintype.ofFinite (columnGroup t)
  change wordRestrict i j (∑ g : columnGroup t,
    signC (g : Equiv.Perm (Fin n)) • wordRep n (μ.colLen 0)
      (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1)) (rowWord s) = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    wordRep_single, wordRestrict_single, he]
  simp

lemma column_viaEmbedding {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (h : ν ≤ μ) (g : columnGroup s) :
    (g : Equiv.Perm (Fin a)).viaEmbedding (tableauInclusion s t h) ∈ columnGroup t := by
  intro k
  by_cases hk : k ∈ Set.range (tableauInclusion s t h)
  · obtain ⟨l, rfl⟩ := hk
    rw [Equiv.Perm.viaEmbedding_apply]
    simpa only [tableauInclusion_cell] using g.property l
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hk]

lemma signC_viaEmbedding {a n : ℕ} (i : Fin a ↪ Fin n) (g : Equiv.Perm (Fin a)) :
    signC (g.viaEmbedding i) = signC g := by
  classical
  simp [signC_def, Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]

lemma strip_contraction_pair {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    dotProduct (wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
      (polytabloid t)) (polytabloid s) ≠ 0 := by
  classical
  let i := tableauInclusion s t hs.1
  let j := rowLetterInclusion hs.1
  let x := wordRestrict i j (polytabloid t)
  have hx (g : columnGroup s) : wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a)) x =
      signC (g : Equiv.Perm (Fin a)) • x := by
    rw [← wordRestrict_equivariant i j ((g : Equiv.Perm (Fin a)).viaEmbedding i)
      (g : Equiv.Perm (Fin a)) (Equiv.Perm.viaEmbedding_apply _ _) (polytabloid t)]
    rw [polytabloid_alternating t ⟨_, column_viaEmbedding s t hs.1 g⟩]
    rw [map_smul, signC_viaEmbedding]
  rw [← columnAlt_coefficient]
  let := Fintype.ofFinite (columnGroup s)
  have he : columnAlt s x = (Fintype.card (columnGroup s) : ℂ) • x := by
    change (∑ g : columnGroup s, signC (g : Equiv.Perm (Fin a)) •
      wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a))) x = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul,
      signC_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  change columnAlt s x (rowWord s) ≠ 0
  rw [he]
  change (Fintype.card (columnGroup s) : ℂ) *
    wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1) (polytabloid t) (rowWord s) ≠ 0
  rw [strip_contraction_coefficient s t hs, mul_one]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/- Positive horizontal-strip Pieri map, equivariant for the full Young subgroup. -/
theorem pieri_strip_restriction {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, F ≠ 0 ∧
      ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t hs.1 k) = tableauInclusion s t hs.1 (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x) := by
  let pr := subrepProject (spechtSub s) (fun _ hx => cyclic_star _ (polytabloid_real s) hx)
  let T := wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
  let F := pr.toLinearMap.comp (T.comp (spechtSub t).toSubmodule.subtype)
  refine ⟨F, ?_, ?_⟩
  · intro hF
    have hp := subrepProject_pair (spechtSub s)
      (fun _ hx => cyclic_star _ (polytabloid_real s) hx)
      (T (polytabloid t)) ⟨polytabloid s, mem_cyclic _ _⟩
    have he : pr (T (polytabloid t)) = 0 := by
      exact congrArg (fun L : Specht t →ₗ[ℂ] Specht s => L ⟨polytabloid t, mem_cyclic _ _⟩) hF
    rw [he] at hp
    exact strip_contraction_pair s t hs (hp.symm.trans (zero_dotProduct _))
  · intro g h hh x
    change pr (T (wordRep n (μ.colLen 0) g x.val)) = spechtRep s h (pr (T x.val))
    rw [wordRestrict_equivariant _ _ g h hh x.val]
    exact LinearMap.congr_fun (pr.isIntertwining' h) (T x.val)

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma pieri_strip_surjective {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, Function.Surjective F ∧
      ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t hs.1 k) = tableauInclusion s t hs.1 (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x) := by
  obtain ⟨F,hF,he⟩ := pieri_strip_restriction s t hs
  let E : Representation.IntertwiningMap
      ((spechtRep t).comp (Equiv.Perm.viaEmbeddingHom (tableauInclusion s t hs.1)))
      (spechtRep s) :=
    { toLinearMap := F
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro x
        exact he _ h (fun k => Equiv.Perm.viaEmbedding_apply _ _ k) x }
  have hE : E ≠ 0 := by
    intro hz
    exact hF (congrArg Representation.IntertwiningMap.toLinearMap hz)
  have := specht_irreducible s
  exact ⟨F, (Representation.IsIrreducible.surjective_or_eq_zero E).resolve_right hE, he⟩

def restrictPerm {a n : ℕ} (i : Fin a ↪ Fin n) (g : Equiv.Perm (Fin n))
    (hg : ∀ x, g x ∈ Set.range i ↔ x ∈ Set.range i) : Equiv.Perm (Fin a) :=
  (Equiv.ofInjective i i.injective).trans ((g.subtypePerm hg).trans
    (Equiv.ofInjective i i.injective).symm)

lemma restrictPerm_apply {a n : ℕ} (i : Fin a ↪ Fin n) (g : Equiv.Perm (Fin n))
    (hg : ∀ x, g x ∈ Set.range i ↔ x ∈ Set.range i) (k : Fin a) :
    i (restrictPerm i g hg k) = g (i k) := by
  change ((Equiv.ofInjective i i.injective)
    ((Equiv.ofInjective i i.injective).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma tableauInclusion_trans {a b n : ℕ} {ν η μ : YoungDiagram}
    (s : Tableau a ν) (u : Tableau b η) (t : Tableau n μ)
    (h₁ : ν ≤ η) (h₂ : η ≤ μ) (k : Fin a) :
    tableauInclusion u t h₂ (tableauInclusion s u h₁ k) =
      tableauInclusion s t (h₁.trans h₂) k := by
  change t.symm ⟨(u (u.symm ⟨(s k).val, _⟩)).val, _⟩ = t.symm ⟨(s k).val, _⟩
  simp only [Equiv.apply_symm_apply]

def extendColor {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ) : Fin n → ℕ :=
  fun x => if h : x ∈ Set.range i then c ((Equiv.ofInjective i i.injective).symm ⟨x,h⟩) else q

lemma extendColor_apply {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (x : Fin a) : extendColor i c q (i x) = c x := by
  classical
  unfold extendColor
  rw [dite_eq_left ⟨x,rfl⟩]
  congr 1
  exact (Equiv.ofInjective i i.injective).symm_apply_apply x

lemma extendColor_mem {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) (x : Fin n) :
    extendColor i c (q+1) x ≤ q ↔ x ∈ Set.range i := by
  classical
  unfold extendColor
  split_ifs with h
  · exact iff_of_true (hc _) h
  · simp [h]

lemma extendColor_le {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) (x : Fin n) : extendColor i c (q+1) x ≤ q+1 := by
  classical
  unfold extendColor
  split_ifs
  · exact (hc _).trans (Nat.le_succ q)
  · exact le_rfl

lemma extendColor_count_old {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q j : ℕ)
    (hj : j ≠ q) :
    (Finset.univ.filter (fun x => extendColor i c q x = j)).card =
      (Finset.univ.filter (fun x => c x = j)).card := by
  classical
  symm
  apply Finset.card_bij (fun x _ => i x)
  · intro x hx
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, extendColor_apply] using hx
  · intro x hx y hy hxy
    exact i.injective hxy
  · intro y hy
    have hyj := (Finset.mem_filter.mp hy).2
    have hym : y ∈ Set.range i := by
      by_contra hn
      simp only [extendColor, dite_eq_right hn] at hyj
      exact hj hyj.symm
    obtain ⟨x,rfl⟩ := hym
    refine ⟨x, ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, extendColor_apply] using hyj

lemma extendColor_count_new {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) :
    (Finset.univ.filter (fun x => extendColor i c (q+1) x = q+1)).card = n-a := by
  classical
  have he : Finset.univ.filter (fun x => extendColor i c (q+1) x = q+1) =
      Finset.univ \ Finset.univ.map i := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_map]
    change extendColor i c (q+1) x = q+1 ↔ ¬ x ∈ Set.range i
    rw [← extendColor_mem i c q hc x]
    have hl := extendColor_le i c q hc x
    omega
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_map, Finset.card_univ, Fintype.card_fin]

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

inductive SizedStripChain : List ℕ → YoungDiagram → YoungDiagram → Prop
  | nil (μ) : SizedStripChain [] μ μ
  | snoc {bs ν η μ b} : SizedStripChain bs ν η → HorizontalStrip η μ →
      η.card + b = μ.card → SizedStripChain (bs ++ [b]) ν μ

lemma SizedStripChain.le {bs ν μ} (hs : SizedStripChain bs ν μ) : ν ≤ μ := by
  induction hs with
  | nil => exact le_rfl
  | snoc hs hh hc ih => exact ih.trans hh.1

abbrev shapeTableau (μ : YoungDiagram) : Tableau μ.card μ := canonicalTableau μ rfl

lemma tableauInclusion_self {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (k : Fin n) :
    tableauInclusion t t le_rfl k = k := by
  change t.symm (t k) = k
  exact t.symm_apply_apply k

/- Iterated positive Pieri, with an explicit coloring of the added strips.
The map is surjective and equivariant for all permutations preserving each
strip, not just for the smaller symmetric group. -/
theorem stripChain_restriction {bs ν μ} (hs : SizedStripChain bs ν μ) :
    ∃ (c : Fin μ.card → ℕ) (F : Specht (shapeTableau μ) →ₗ[ℂ] Specht (shapeTableau ν)),
      Function.Surjective F ∧
      (∀ i, c i ≤ bs.length) ∧
      (∀ i, c i = 0 ↔ i ∈ Set.range (tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le)) ∧
      (∀ j (hj : j < bs.length), (Finset.univ.filter (fun i => c i = j+1)).card = bs[j]) ∧
      (∀ (g : Equiv.Perm (Fin μ.card)) (h : Equiv.Perm (Fin ν.card)),
        (∀ i, c (g i) = c i) →
        (∀ k, g (tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le k) =
          tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le (h k)) →
        ∀ x, F (spechtRep (shapeTableau μ) g x) = spechtRep (shapeTableau ν) h (F x)) := by
  classical
  induction hs with
  | nil ν =>
    refine ⟨fun _ => 0, LinearMap.id, Function.surjective_id, by simp, ?_, ?_, ?_⟩
    · intro i
      constructor
      · intro _; exact ⟨i,tableauInclusion_self _ i⟩
      · intro _; rfl
    · intro j hj; simp at hj
    · intro g h hc he x
      have hh : g = h := by
        apply Equiv.ext
        intro k
        simpa only [tableauInclusion_self] using he k
      subst h
      rfl
  | @snoc bs ν η μ b hs hh hcard ih =>
    obtain ⟨c,F,hF,hc,hzero,hcount,he⟩ := ih
    obtain ⟨P,hP,hPe⟩ := pieri_strip_surjective (shapeTableau η) (shapeTableau μ) hh
    let i := tableauInclusion (shapeTableau η) (shapeTableau μ) hh.1
    let c' := extendColor i c (bs.length+1)
    refine ⟨c', F.comp P, hF.comp hP, ?_, ?_, ?_, ?_⟩
    · intro k
      simpa only [List.length_append, List.length_singleton] using extendColor_le i c bs.length hc k
    · intro k
      constructor
      · intro hk
        change extendColor i c (bs.length+1) k = 0 at hk
        have hr : k ∈ Set.range i := (extendColor_mem i c bs.length hc k).mp (by omega)
        obtain ⟨l,rfl⟩ := hr
        have hl : c l = 0 := (extendColor_apply i c _ l).symm.trans hk
        obtain ⟨j,hj⟩ := (hzero l).mp hl
        refine ⟨j, ?_⟩
        rw [← tableauInclusion_trans (shapeTableau ν) (shapeTableau η) (shapeTableau μ) hs.le hh.1]
        exact congrArg i hj
      · rintro ⟨j,rfl⟩
        rw [← tableauInclusion_trans (shapeTableau ν) (shapeTableau η) (shapeTableau μ) hs.le hh.1]
        change extendColor i c _ (i _) = 0
        rw [extendColor_apply]
        exact (hzero _).mpr ⟨j,rfl⟩
    · intro j hj
      have hjle : j ≤ bs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      rcases lt_or_eq_of_le hjle with hjlt | rfl
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = j+1)).card = _
        rw [extendColor_count_old i c (bs.length+1) (j+1) (by omega), hcount j hjlt,
          List.getElem_append_left hjlt]
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = bs.length+1)).card = _
        rw [extendColor_count_new i c bs.length hc]
        simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
        omega
    · intro g h hg hgi x
      have hgmem : ∀ k, g k ∈ Set.range i ↔ k ∈ Set.range i := by
        intro k
        rw [← extendColor_mem i c bs.length hc, ← extendColor_mem i c bs.length hc]
        exact (congrArg (fun c => c ≤ bs.length) (hg k)).to_iff
      let k := restrictPerm i g hgmem
      have hik (l) : i (k l) = g (i l) := restrictPerm_apply i g hgmem l
      have hkcolor (l) : c (k l) = c l := by
        rw [← extendColor_apply i c (bs.length+1) (k l), hik, ← extendColor_apply i c (bs.length+1) l]
        exact hg (i l)
      have hkbase (l) : k (tableauInclusion (shapeTableau ν) (shapeTableau η) hs.le l) =
          tableauInclusion (shapeTableau ν) (shapeTableau η) hs.le (h l) := by
        apply i.injective
        rw [hik]
        change g (tableauInclusion (shapeTableau η) (shapeTableau μ) hh.1 _) =
          tableauInclusion (shapeTableau η) (shapeTableau μ) hh.1 _
        rw [tableauInclusion_trans, tableauInclusion_trans]
        exact hgi l
      change F (P (spechtRep (shapeTableau μ) g x)) = _
      rw [hPe g k (fun l => (hik l).symm), he k h hkcolor hkbase]
      rfl



theorem stripChain_restriction_any {bs ν μ} (hs : SizedStripChain bs ν μ)
    {a n : ℕ} (s : Tableau a ν) (t : Tableau n μ) :
    ∃ (c : Fin n → ℕ) (F : Specht t →ₗ[ℂ] Specht s),
      Function.Surjective F ∧
      (∀ i, c i ≤ bs.length) ∧
      (∀ i, c i = 0 ↔ i ∈ Set.range (tableauInclusion s t hs.le)) ∧
      (∀ j (hj : j < bs.length), (Finset.univ.filter (fun i => c i = j+1)).card = bs[j]) ∧
      (∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ i, c (g i) = c i) →
        (∀ k, g (tableauInclusion s t hs.le k) =
          tableauInclusion s t hs.le (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x)) := by
  classical
  induction hs generalizing a n with
  | nil ν =>
    obtain ⟨F,hF,hFe⟩ := pieri_strip_surjective s t
      (show HorizontalStrip ν ν from ⟨le_rfl, by intros x hx hn; exact False.elim (hn hx)⟩)
    refine ⟨fun _ => 0, F, hF, by simp, ?_, ?_, ?_⟩
    · intro i
      constructor
      · intro _
        refine ⟨s.symm (t i), ?_⟩
        change t.symm ⟨(s (s.symm (t i))).val, _⟩ = i
        simp only [Equiv.apply_symm_apply]
        exact t.symm_apply_apply i
      · intro _; rfl
    · intro j hj; simp at hj
    · intro g h hc he x
      exact hFe g h he x
  | @snoc bs ν η μ b hs hh hcard ih =>
    obtain ⟨c,F,hF,hc,hzero,hcount,he⟩ := ih s (shapeTableau η)
    obtain ⟨P,hP,hPe⟩ := pieri_strip_surjective (shapeTableau η) t hh
    let i := tableauInclusion (shapeTableau η) t hh.1
    let c' := extendColor i c (bs.length+1)
    refine ⟨c', F.comp P, hF.comp hP, ?_, ?_, ?_, ?_⟩
    · intro k
      simpa only [List.length_append, List.length_singleton] using extendColor_le i c bs.length hc k
    · intro k
      constructor
      · intro hk
        change extendColor i c (bs.length+1) k = 0 at hk
        have hr : k ∈ Set.range i := (extendColor_mem i c bs.length hc k).mp (by omega)
        obtain ⟨l,rfl⟩ := hr
        have hl : c l = 0 := (extendColor_apply i c _ l).symm.trans hk
        obtain ⟨j,hj⟩ := (hzero l).mp hl
        refine ⟨j, ?_⟩
        rw [← tableauInclusion_trans s (shapeTableau η) t hs.le hh.1]
        exact congrArg i hj
      · rintro ⟨j,rfl⟩
        rw [← tableauInclusion_trans s (shapeTableau η) t hs.le hh.1]
        change extendColor i c _ (i _) = 0
        rw [extendColor_apply]
        exact (hzero _).mpr ⟨j,rfl⟩
    · intro j hj
      have hjle : j ≤ bs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      rcases lt_or_eq_of_le hjle with hjlt | rfl
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = j+1)).card = _
        rw [extendColor_count_old i c (bs.length+1) (j+1) (by omega), hcount j hjlt,
          List.getElem_append_left hjlt]
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = bs.length+1)).card = _
        rw [extendColor_count_new i c bs.length hc]
        simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
        have ht : n = μ.card := by
          have := Fintype.card_congr t
          simpa only [Fintype.card_fin, Fintype.card_coe] using this
        omega
    · intro g h hg hgi x
      have hgmem : ∀ k, g k ∈ Set.range i ↔ k ∈ Set.range i := by
        intro k
        rw [← extendColor_mem i c bs.length hc, ← extendColor_mem i c bs.length hc]
        exact (congrArg (fun c => c ≤ bs.length) (hg k)).to_iff
      let k := restrictPerm i g hgmem
      have hik (l) : i (k l) = g (i l) := restrictPerm_apply i g hgmem l
      have hkcolor (l) : c (k l) = c l := by
        rw [← extendColor_apply i c (bs.length+1) (k l), hik, ← extendColor_apply i c (bs.length+1) l]
        exact hg (i l)
      have hkbase (l) : k (tableauInclusion s (shapeTableau η) hs.le l) =
          tableauInclusion s (shapeTableau η) hs.le (h l) := by
        apply i.injective
        rw [hik]
        change g (tableauInclusion (shapeTableau η) t hh.1 _) =
          tableauInclusion (shapeTableau η) t hh.1 _
        rw [tableauInclusion_trans, tableauInclusion_trans]
        exact hgi l
      change F (P (spechtRep t g x)) = _
      rw [hPe g k (fun l => (hik l).symm), he k h hkcolor hkbase]
      rfl

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Place the smaller tableau on any chosen block, with the remaining strip
colors on its complement. No transitivity or induction rule is assumed. -/
theorem placed_strip_restriction {n a b : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    ∃ (c : Fin b → Fin bs.length) (F : Specht t →ₗ[ℂ] Specht s), Function.Surjective F ∧
      ∀ (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)), c ∘ q = c →
        ∀ x, F (spechtRep t (sumPerm e h q) x) = spechtRep s h (F x) := by
  classical
  obtain ⟨c,F,hF,hcb,hcz,hcount,hFe⟩ := stripChain_restriction_any hs s t
  let i := tableauInclusion s t hs.le
  let l : Fin a → Fin n := fun j => e.symm (Sum.inl j)
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair l i
    (fun x y h => Sum.inl.inj (e.symm.injective h)) i.injective
  have hcL (j : Fin a) : c (p (e.symm (Sum.inl j))) = 0 := by
    rw [show p (e.symm (Sum.inl j)) = i j from hp j]
    exact (hcz _).mpr ⟨j,rfl⟩
  have hcRpos (j : Fin b) : 0 < c (p (e.symm (Sum.inr j))) := by
    by_contra hn
    have hz : c (p (e.symm (Sum.inr j))) = 0 := by omega
    obtain ⟨k,hk⟩ := (hcz _).mp hz
    have hh : e.symm (Sum.inl k) = e.symm (Sum.inr j) := p.injective ((hp k).trans hk)
    have := e.symm.injective hh
    cases this
  let cb : Fin b → Fin bs.length := fun j => ⟨c (p (e.symm (Sum.inr j)))-1, by
    have := hcRpos j
    have := hcb (p (e.symm (Sum.inr j)))
    omega⟩
  have hcR (j : Fin b) : c (p (e.symm (Sum.inr j))) = (cb j).val+1 := by
    have := hcRpos j
    change _ = (c (p (e.symm (Sum.inr j)))-1)+1
    omega
  let F' := F.comp (spechtRep t p)
  have hP : Function.Surjective (spechtRep t p) := by
    intro x
    refine ⟨spechtRep t p⁻¹ x, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  refine ⟨cb,F',hF.comp hP, ?_⟩
  intro h q hq x
  let g := p * sumPerm e h q * p⁻¹
  have hgL (j : Fin a) : g (p (e.symm (Sum.inl j))) = p (e.symm (Sum.inl (h j))) := by
    simp [g]
  have hgR (j : Fin b) : g (p (e.symm (Sum.inr j))) = p (e.symm (Sum.inr (q j))) := by
    simp [g]
  have hgc (j : Fin n) : c (g j) = c j := by
    obtain ⟨z,rfl⟩ := p.surjective j
    obtain ⟨z,rfl⟩ := e.symm.surjective z
    cases z with
    | inl j => rw [hgL,hcL,hcL]
    | inr j =>
      rw [hgR,hcR,hcR]
      exact congrArg (fun x : Fin bs.length => x.val+1) (congrFun hq j)
  have hgi (j : Fin a) : g (i j) = i (h j) := by rw [← hp j,← hp (h j)]; exact hgL j
  change F (spechtRep t p (spechtRep t (sumPerm e h q) x)) = spechtRep s h (F (spechtRep t p x))
  have hmul : p * sumPerm e h q = g * p := by simp [g,mul_assoc]
  rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply]
  exact hFe g h hgc hgi _

end Saxl

namespace Saxl

/- Required support transfer from a genuine iterated horizontal-strip
restriction and genuine independent high/band cyclic factors. -/
theorem strip_product_support {n a b d : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hv : v ∈ alphabetSub a d A)
    (hu : u ∈ alphabetSub b d (fun z => ¬A z))
    (f : Representation.IntertwiningMap (spechtRep s) (cyclic (wordRep a d) v).toRepresentation)
    (hf : f ≠ 0)
    (hband : ∀ (η : YoungDiagram) (r : Tableau b η), η.colLen 0 ≤ bs.length →
      ∃ F : Representation.IntertwiningMap (spechtRep r) (cyclic (wordRep b d) u).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation, F ≠ 0 := by
  classical
  obtain ⟨c,F,hF,hFe⟩ := placed_strip_restriction hs s t e
  let G := (subrepInclusion (cyclic (wordRep a d) v)).comp f
  let F₀ : Specht t →ₗ[ℂ] WordSpace a d := G.toLinearMap.comp F
  have hF₀ : F₀ ≠ 0 := by
    intro hz
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := hF y
    apply Subtype.ext
    exact LinearMap.congr_fun hz x
  have hFb (q : Equiv.Perm (Fin b)) (hq : c ∘ q = c) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e 1 q) x) = F₀ x := by
    change G (F (spechtRep t (sumPerm e 1 q) x)) = G (F x)
    rw [hFe 1 q hq, map_one]
    rfl
  have hFa (h : Equiv.Perm (Fin a)) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e h 1) x) = wordRep a d h (F₀ x) := by
    change G (F (spechtRep t (sumPerm e h 1) x)) = wordRep a d h (G (F x))
    rw [hFe h 1 rfl]
    exact LinearMap.congr_fun (G.isIntertwining' h) (F x)
  let T := bandOrbitMap e (spechtRep t) c F₀
  have hTm (x : Specht t) (w : Fin b → Fin bs.length) : T x w ∈ cyclic (wordRep a d) v := by
    change (∑ g : Equiv.Perm (Fin b), _) ∈ (cyclic (wordRep a d) v).toSubmodule
    apply Submodule.sum_mem
    intro g hg
    apply Submodule.smul_mem
    exact (f (F (spechtRep t (sumPerm e 1 g⁻¹) x))).property
  obtain ⟨L,hL,hLe,hLm,hLs⟩ := bandGlue_sector_exists e (spechtRep t) v u A hv hu hband T
    (bandOrbitMap_nonzero e (spechtRep t) c F₀ hF₀ hFb)
    (bandOrbitMap_equivariant e (spechtRep t) (wordRep a d) c F₀ hFa) hTm
  apply sector_support_transfer (spechtRep t) (fun i => (e i).isLeft = true) A
    (positionProduct e v u) L hL _ hLm
  · intro x w hw
    by_contra hn
    exact hw (hLs x w hn)
  · intro g hg x
    let g' : sectorGroup (fun i => (e i).isLeft = true) := ⟨g,hg⟩
    have heq : sumPerm e (leftRestriction e g') (rightRestriction e g') = g := sumPerm_restrictions e g'
    rw [← heq]
    exact hLe _ _ x

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
def rowPrefix (μ : YoungDiagram) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, μ.rowLen i

def Dominates (μ ν : YoungDiagram) : Prop := ∀ k, rowPrefix ν k ≤ rowPrefix μ k

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
def stripRow (μ : YoungDiagram) (t i : ℕ) := μ.rowLen i - t + min t (μ.rowLen (i+1))

lemma stripRow_bounds (μ : YoungDiagram) (t i : ℕ) :
    μ.rowLen (i+1) ≤ stripRow μ t i ∧ stripRow μ t i ≤ μ.rowLen i := by
  have h := μ.rowLen_anti i (i+1) (by omega)
  dsimp [stripRow]
  omega

lemma stripRow_antitone (μ : YoungDiagram) (t : ℕ) : Antitone (stripRow μ t) := by
  intro i j hij
  exact Nat.add_le_add (Nat.sub_le_sub_right (μ.rowLen_anti i j hij) t)
    (min_le_min_left t (μ.rowLen_anti (i+1) (j+1) (by omega)))

def stripRemove (μ : YoungDiagram) (t : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun x => x.2 < stripRow μ t x.1)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨μ.up_left_mem hxy.1 hxy.2 hy.1,
      lt_of_le_of_lt hxy.2 (lt_of_lt_of_le hy.2 (stripRow_antitone μ t hxy.1))⟩

@[simp] lemma mem_stripRemove {μ : YoungDiagram} {t i j : ℕ} :
    (i,j) ∈ stripRemove μ t ↔ j < stripRow μ t i := by
  change (i,j) ∈ μ.cells.filter _ ↔ _
  simp only [Finset.mem_filter, YoungDiagram.mem_cells]
  exact ⟨And.right, fun h => ⟨YoungDiagram.mem_iff_lt_rowLen.mpr
    (lt_of_lt_of_le h (stripRow_bounds μ t i).2), h⟩⟩

@[simp] lemma stripRemove_rowLen (μ : YoungDiagram) (t i : ℕ) :
    (stripRemove μ t).rowLen i = stripRow μ t i := by
  have hh : ∀ j, j < (stripRemove μ t).rowLen i ↔ j < stripRow μ t i := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_stripRemove]
  have h₁ := hh ((stripRemove μ t).rowLen i)
  have h₂ := hh (stripRow μ t i)
  omega

lemma stripRemove_le (μ : YoungDiagram) (t : ℕ) : stripRemove μ t ≤ μ := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

lemma stripRemove_horizontal (μ : YoungDiagram) (t : ℕ) : HorizontalStrip (stripRemove μ t) μ := by
  refine ⟨stripRemove_le μ t, ?_⟩
  intro x hx hxn y hy hyn hcol
  have hhx := YoungDiagram.mem_iff_lt_rowLen.mp hx
  have hhy := YoungDiagram.mem_iff_lt_rowLen.mp hy
  have hnx : stripRow μ t x.1 ≤ x.2 := le_of_not_gt (fun h => hxn (mem_stripRemove.mpr h))
  have hny : stripRow μ t y.1 ≤ y.2 := le_of_not_gt (fun h => hyn (mem_stripRemove.mpr h))
  have hr : x.1 = y.1 := by
    rcases lt_trichotomy x.1 y.1 with hr | hr | hr
    · have hh := μ.rowLen_anti (x.1+1) y.1 (by omega)
      have hb := (stripRow_bounds μ t x.1).1
      omega
    · exact hr
    · have hh := μ.rowLen_anti (y.1+1) x.1 (by omega)
      have hb := (stripRow_bounds μ t y.1).1
      omega
  exact Prod.ext hr hcol

lemma stripRemove_prefix (μ : YoungDiagram) (t k : ℕ) :
    rowPrefix (stripRemove μ t) k + min t (μ.rowLen 0) =
      rowPrefix μ k + min t (μ.rowLen k) := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    have hr : (stripRemove μ t).rowLen k + min t (μ.rowLen k) =
        μ.rowLen k + min t (μ.rowLen (k+1)) := by
      rw [stripRemove_rowLen]
      dsimp [stripRow]
      omega
    simp only [rowPrefix, Finset.sum_range_succ] at ih ⊢
    omega

lemma stripRemove_card (μ : YoungDiagram) (t : ℕ) :
    (stripRemove μ t).card + min t (μ.rowLen 0) = μ.card := by
  have hh := stripRemove_prefix μ t (μ.colLen 0)
  rw [rowPrefix_eq_card μ le_rfl, rowLen_zero_of_height_le μ le_rfl, min_zero, add_zero] at hh
  have ht : (stripRemove μ t).colLen 0 ≤ μ.colLen 0 := by
    by_contra h
    have hm : (μ.colLen 0, 0) ∈ stripRemove μ t := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hh := YoungDiagram.mem_iff_lt_colLen.mp (stripRemove_le μ t hm)
    omega
  rwa [rowPrefix_eq_card _ ht] at hh

lemma stripRemove_full (μ : YoungDiagram) (i : ℕ) :
    (stripRemove μ (μ.rowLen 0)).rowLen i = μ.rowLen (i+1) := by
  rw [stripRemove_rowLen]
  have hi := μ.rowLen_anti 0 i (Nat.zero_le _)
  have hs := μ.rowLen_anti 0 (i+1) (Nat.zero_le _)
  dsimp [stripRow]
  omega


lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  simp [rowPrefix, Finset.sum_range_succ]

lemma rowPrefix_le_card (μ : YoungDiagram) (k : ℕ) : rowPrefix μ k ≤ μ.card := by
  rw [← rowPrefix_eq_card μ (Nat.le_max_left _ k)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_max_right _ _))

lemma rowPrefix_mono (μ : YoungDiagram) {k l : ℕ} (h : k ≤ l) :
    rowPrefix μ k ≤ rowPrefix μ l :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

def rowTruncate (μ : YoungDiagram) (k : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun x => x.1 < k)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨μ.up_left_mem hxy.1 hxy.2 hy.1, lt_of_le_of_lt hxy.1 hy.2⟩

@[simp] lemma mem_rowTruncate {μ : YoungDiagram} {k i j : ℕ} :
    (i,j) ∈ rowTruncate μ k ↔ (i,j) ∈ μ ∧ i < k := by
  change (i,j) ∈ μ.cells.filter (fun x => x.1 < k) ↔ (i,j) ∈ μ.cells ∧ i < k
  exact Finset.mem_filter

lemma rowTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (rowTruncate μ k).rowLen i = if i < k then μ.rowLen i else 0 := by
  have hh : ∀ j, j < (rowTruncate μ k).rowLen i ↔ j < if i < k then μ.rowLen i else 0 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_rowTruncate, YoungDiagram.mem_iff_lt_rowLen]
    split_ifs <;> simp_all
  have h₁ := hh ((rowTruncate μ k).rowLen i)
  have h₂ := hh (if i < k then μ.rowLen i else 0)
  omega

lemma rowTruncate_height (μ : YoungDiagram) (k : ℕ) : (rowTruncate μ k).colLen 0 ≤ k := by
  by_contra h
  have hm : (k,0) ∈ rowTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  exact Nat.lt_irrefl k (mem_rowTruncate.mp hm).2

lemma rowTruncate_prefix (μ : YoungDiagram) (k q : ℕ) (hq : q ≤ k) :
    rowPrefix (rowTruncate μ k) q = rowPrefix μ q := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [rowTruncate_rowLen, ite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hi) hq)]

lemma rowTruncate_card (μ : YoungDiagram) (k : ℕ) :
    (rowTruncate μ k).card = rowPrefix μ k := by
  rw [← rowPrefix_eq_card _ (rowTruncate_height μ k), rowTruncate_prefix _ _ _ le_rfl]

lemma dominates_stripRemove_last (θ τ : YoungDiagram) (k : ℕ)
    (hh : θ.colLen 0 ≤ k+1) (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    (stripRemove τ (θ.rowLen k)).card = (rowTruncate θ k).card ∧
      Dominates (stripRemove τ (θ.rowLen k)) (rowTruncate θ k) := by
  have hw : θ.rowLen k ≤ τ.rowLen 0 := by
    have hh := hd 1
    simp only [rowPrefix, Finset.sum_range_one] at hh
    exact (θ.rowLen_anti 0 k (Nat.zero_le _)).trans hh
  have hθ : (rowTruncate θ k).card + θ.rowLen k = θ.card := by
    rw [rowTruncate_card, ← rowPrefix_succ, rowPrefix_eq_card θ hh]
  have hτ : (stripRemove τ (θ.rowLen k)).card + θ.rowLen k = τ.card := by
    simpa only [min_eq_left hw] using stripRemove_card τ (θ.rowLen k)
  have hcard : (stripRemove τ (θ.rowLen k)).card = (rowTruncate θ k).card := by omega
  refine ⟨hcard, ?_⟩
  have hsmall (q : ℕ) (hq : q ≤ k) : rowPrefix θ q ≤ rowPrefix (stripRemove τ (θ.rowLen k)) q := by
    have he := stripRemove_prefix τ (θ.rowLen k) q
    rw [min_eq_left hw] at he
    by_cases hr : θ.rowLen k ≤ τ.rowLen q
    · rw [min_eq_left hr] at he
      have hh := hd q
      omega
    · rw [min_eq_right (by omega : τ.rowLen q ≤ θ.rowLen k)] at he
      have hsq := hd (q+1)
      rw [rowPrefix_succ, rowPrefix_succ] at hsq
      have ht := θ.rowLen_anti q k hq
      omega
  intro q
  by_cases hq : q ≤ k
  · rw [rowTruncate_prefix _ _ _ hq]
    exact hsmall q hq
  · have hle := rowPrefix_le_card (rowTruncate θ k) q
    rw [rowTruncate_card] at hle
    exact hle.trans ((hsmall k le_rfl).trans (rowPrefix_mono _ (by omega)))

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Horizontal-strip chains recording the exact ordered strip sizes. -/
def rowWeights (θ : YoungDiagram) : ℕ → List ℕ
  | 0 => []
  | k+1 => rowWeights θ k ++ [θ.rowLen k]

lemma rowWeights_congr (θ τ : YoungDiagram) (k : ℕ)
    (he : ∀ i < k, θ.rowLen i = τ.rowLen i) : rowWeights θ k = rowWeights τ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rowWeights, rowWeights, ih (fun i hi => he i (by omega)), he k (by omega)]

lemma card_zero_iff_bot (μ : YoungDiagram) : μ.card = 0 ↔ μ = ⊥ := by
  change μ.cells.card = 0 ↔ _
  rw [Finset.card_eq_zero]
  constructor
  · intro h; exact YoungDiagram.ext h
  · intro h; subst μ; rfl

/- The actual constructive sufficiency step in Young's rule. No tableau,
Pieri, or representation hypothesis is assumed by this combinatorial theorem. -/
theorem sizedStripChain_of_dominates (θ τ : YoungDiagram) (k : ℕ)
    (hh : θ.colLen 0 ≤ k) (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    SizedStripChain (rowWeights θ k) ⊥ τ := by
  induction k generalizing θ τ with
  | zero =>
    have hcθ : θ.card = 0 := by
      have he := rowPrefix_eq_card θ hh
      simpa [rowPrefix] using he.symm
    have ht : τ = ⊥ := (card_zero_iff_bot τ).mp (hc.trans hcθ)
    subst τ
    exact SizedStripChain.nil ⊥
  | succ k ih =>
    obtain ⟨hcν,hdν⟩ := dominates_stripRemove_last θ τ k hh hc hd
    have hs := ih (rowTruncate θ k) (stripRemove τ (θ.rowLen k))
      (rowTruncate_height θ k) hcν hdν
    have he : rowWeights (rowTruncate θ k) k = rowWeights θ k := by
      apply rowWeights_congr
      intro i hi
      rw [rowTruncate_rowLen, ite_eq_left hi]
    rw [he] at hs
    apply SizedStripChain.snoc hs (stripRemove_horizontal τ (θ.rowLen k))
    have hw : θ.rowLen k ≤ τ.rowLen 0 := by
      have hp := hd 1
      simp only [rowPrefix, Finset.sum_range_one] at hp
      exact (θ.rowLen_anti 0 k (Nat.zero_le _)).trans hp
    simpa only [min_eq_left hw] using stripRemove_card τ (θ.rowLen k)



lemma rowWeights_length (θ : YoungDiagram) (k : ℕ) : (rowWeights θ k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rowWeights, List.length_append, List.length_singleton, ih]

lemma rowWeights_getElem (θ : YoungDiagram) (k j : ℕ) (hj : j < k) :
    (rowWeights θ k)[j]'(by rw [rowWeights_length]; exact hj) = θ.rowLen j := by
  induction k with
  | zero => omega
  | succ k ih =>
    change (rowWeights θ k ++ [θ.rowLen k])[j]'(by simpa only [List.length_append, List.length_singleton, rowWeights_length] using hj) = θ.rowLen j
    by_cases h : j < k
    · rw [List.getElem_append_left (by rwa [rowWeights_length]), ih h]
    · have he : j = k := by omega
      subst j
      rw [List.getElem_append_right (by rw [rowWeights_length])]
      simp only [rowWeights_length, Nat.sub_self, List.getElem_singleton]

lemma perm_of_equal_content {n d : ℕ} (a b : Fin n → Fin d)
    (h : ∀ j, (Finset.univ.filter (fun i => a i = j)).card =
      (Finset.univ.filter (fun i => b i = j)).card) :
    ∃ g : Equiv.Perm (Fin n), b ∘ g = a := by
  classical
  let e (j) : {i // a i = j} ≃ {i // b i = j} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype] using h j)
  let g := (Equiv.sigmaFiberEquiv a).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv b))
  refine ⟨g, ?_⟩
  funext i
  exact (e (a i) ⟨i,rfl⟩).property

lemma vector_of_invariant_functional {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (l : Module.Dual ℂ (Specht t)) (hl : l ≠ 0)
    (he : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ∀ x, l (spechtRep t g x) = l x) :
    ∃ y : Specht t, y ≠ 0 ∧ ∀ g : Equiv.Perm (Fin n), a ∘ g = a → spechtRep t g y = y := by
  let e := spechtSelfDual t
  refine ⟨e.symm l, ?_, ?_⟩
  · intro hz
    exact hl (e.symm.injective (hz.trans (map_zero _).symm))
  · intro g hg
    have hi : a ∘ (g⁻¹ : Equiv.Perm (Fin n)) = a := by
      funext i
      have hh := congrFun hg (g⁻¹ i)
      simpa using hh.symm
    have hdual : (spechtRep t).dual g l = l := by
      apply LinearMap.ext
      intro x
      exact he g⁻¹ hi x
    have hh := LinearMap.congr_fun (e.symm.isIntertwining' g) l
    change e.symm ((spechtRep t).dual g l) = spechtRep t g (e.symm l) at hh
    rw [hdual] at hh
    exact hh.symm

/- Young's sufficiency in the exact form needed for the repeated-row quotient:
a dominant Specht has a nonzero invariant functional for a word of the
prescribed content. -/
theorem young_invariant_functional (θ τ : YoungDiagram)
    (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    ∃ (a : Fin τ.card → Fin (θ.colLen 0)) (l : Module.Dual ℂ (Specht (shapeTableau τ))),
      l ≠ 0 ∧
      (∀ j, (Finset.univ.filter (fun i => a i = j)).card = θ.rowLen j) ∧
      (∀ g : Equiv.Perm (Fin τ.card), a ∘ g = a →
        ∀ x, l (spechtRep (shapeTableau τ) g x) = l x) := by
  classical
  let bs := rowWeights θ (θ.colLen 0)
  have hs := sizedStripChain_of_dominates θ τ (θ.colLen 0) le_rfl hc hd
  obtain ⟨c,F,hF,hcB,hzero,hcount,he⟩ := stripChain_restriction hs
  have hpos (i) : 0 < c i := by
    have hz := hzero i
    have hn : ¬ i ∈ Set.range (tableauInclusion (shapeTableau ⊥) (shapeTableau τ) hs.le) := by
      rintro ⟨j,hj⟩
      exact Fin.elim0 j
    have hc0 : c i ≠ 0 := fun h => hn (hz.mp h)
    omega
  have hbound (i) : c i ≤ θ.colLen 0 := by simpa only [rowWeights_length] using hcB i
  let a : Fin τ.card → Fin (θ.colLen 0) := fun i => ⟨c i-1, by have hh := hpos i; have ht := hbound i; omega⟩
  let v : Specht (shapeTableau ⊥) := ⟨polytabloid (shapeTableau ⊥), mem_cyclic _ _⟩
  let l₀ := spechtSelfDual (shapeTableau ⊥) v
  have hl₀ : l₀ ≠ 0 := by
    intro hz
    have hh := (spechtSelfDual (shapeTableau ⊥)).injective (hz.trans (map_zero _).symm)
    exact polytabloid_ne_zero _ (congrArg Subtype.val hh)
  let l := l₀.comp F
  have hl : l ≠ 0 := by
    intro hz
    apply hl₀
    apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := hF y
    exact LinearMap.congr_fun hz x
  refine ⟨a,l,hl,?_,?_⟩
  · intro j
    have hj : j.val < (rowWeights θ (θ.colLen 0)).length := by rw [rowWeights_length]; exact j.isLt
    rw [← rowWeights_getElem θ (θ.colLen 0) j.val j.isLt, ← hcount j.val hj]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (⟨c i-1, _⟩ : Fin (θ.colLen 0)) = j ↔ c i = j.val+1
    rw [Fin.ext_iff]
    change c i-1 = j.val ↔ c i = j.val+1
    have hh := hpos i
    omega
  · intro g hg x
    have hcol (i) : c (g i) = c i := by
      have hh := congrArg Fin.val (congrFun hg i)
      change c (g i)-1 = c i-1 at hh
      have hp := hpos i
      have hpg := hpos (g i)
      omega
    have hh := he g 1 hcol (fun k => Fin.elim0 k) x
    change l₀ (F (spechtRep (shapeTableau τ) g x)) = l₀ (F x)
    rw [hh, map_one]
    rfl

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

def equivOfSubrepEq {G : Type uG} {X : Type uX} [Group G] [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ G X} (S T : Subrepresentation ρ) (h : S = T) :
    Representation.Equiv S.toRepresentation T.toRepresentation := by
  subst T
  exact Representation.Equiv.refl _

/- Positive Young rule as a concrete orbit map (including reordered contents). -/
theorem young_orbit_map {n : ℕ} (θ τ : YoungDiagram) (t : Tableau n τ)
    (hc : τ.card = θ.card) (hd : Dominates τ θ)
    (w : Fin n → Fin (θ.colLen 0)) (e : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = e j)).card = θ.rowLen j) :
    ∃ F : Representation.IntertwiningMap (wordRep n (θ.colLen 0)) (spechtRep t),
      F (Pi.single w 1) ≠ 0 := by
  classical
  have hn : τ.card = n := by
    have hh := Fintype.card_congr t
    simpa using hh.symm
  subst n
  obtain ⟨a,l,hl,hac,hle⟩ := young_invariant_functional θ τ hc hd
  obtain ⟨y,hy,hye⟩ := vector_of_invariant_functional (shapeTableau τ) a l hl hle
  let a' := e ∘ a
  have ha' : ∀ g : Equiv.Perm (Fin τ.card), a' ∘ g = a' →
      spechtRep (shapeTableau τ) g y = y := by
    intro g hg
    apply hye g
    funext i
    exact e.injective (congrFun hg i)
  let F := orbitAverage (spechtRep (shapeTableau τ)) a' y
  have hF : F (Pi.single a' 1) ≠ 0 := by
    rw [show F (Pi.single a' 1) = _ from orbitAverage_base _ a' y ha']
    apply smul_ne_zero _ hy
    apply Nat.cast_ne_zero.mpr
    exact Finset.card_ne_zero.mpr ⟨1, by simp⟩
  have hcnt (j : Fin (θ.colLen 0)) :
      (Finset.univ.filter (fun i => w i = j)).card =
        (Finset.univ.filter (fun i => a' i = j)).card := by
    have haeq : Finset.univ.filter (fun i => a' i = j) =
        Finset.univ.filter (fun i => a i = e.symm j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact e.eq_symm_apply.symm
    rw [haeq, hac]
    simpa only [Equiv.apply_symm_apply] using hw (e.symm j)
  obtain ⟨g,hg⟩ := perm_of_equal_content w a' hcnt
  have hwF : F (Pi.single w 1) ≠ 0 := by
    have hw' : Pi.single w (1:ℂ) = wordRep τ.card (θ.colLen 0) g⁻¹ (Pi.single a' 1) := by
      rw [wordRep_single, inv_inv, hg]
    rw [hw', F.isIntertwining]
    intro hz
    apply hF
    have hh := congrArg (spechtRep (shapeTableau τ) g) hz
    rw [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at hh
    exact hh
  have key : ∀ (S T : Subrepresentation (wordRep τ.card (τ.colLen 0))), S = T →
      ∀ F' : Representation.IntertwiningMap (wordRep τ.card (θ.colLen 0)) S.toRepresentation,
        F' (Pi.single w 1) ≠ 0 →
        ∃ G : Representation.IntertwiningMap (wordRep τ.card (θ.colLen 0)) T.toRepresentation,
          G (Pi.single w 1) ≠ 0 := by
    intro S T h F' hF'
    subst h
    exact ⟨F', hF'⟩
  exact key _ _ (spechtSub_tableau_independent _ _) F hwF



def intertwiningRangeEquiv {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f) :
    ρ.Equiv f.range.toRepresentation where
  toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap hf
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (f.isIntertwining' g) x

def staircaseCyclicInclusion (m : ℕ) :
    Representation.IntertwiningMap (staircaseCyclic m).toRepresentation
      ((staircaseTensorMap m).range.toRepresentation) where
  toLinearMap := Submodule.inclusion (staircaseCyclic_le_tensorRange m)
  isIntertwining' _ := rfl

def intertwiningLiftSubrep {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f)
    (S : Subrepresentation σ) (hS : S ≤ f.range) :
    Representation.IntertwiningMap S.toRepresentation ρ := by
  let e : ρ.Equiv f.range.toRepresentation := intertwiningRangeEquiv f hf
  let i : Representation.IntertwiningMap S.toRepresentation f.range.toRepresentation :=
    { toLinearMap := Submodule.inclusion hS, isIntertwining' := fun _ => rfl }
  exact e.symm.toIntertwiningMap.comp i

lemma intertwiningLiftSubrep_injective {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f)
    (S : Subrepresentation σ) (hS : S ≤ f.range) :
    Function.Injective (intertwiningLiftSubrep f hf S hS) := by
  intro x y h
  apply Subtype.ext
  have hh := (intertwiningRangeEquiv f hf).symm.injective h
  exact congrArg (fun z : f.range => (z : Y)) hh

attribute [irreducible] intertwiningLiftSubrep

/- The genuine cyclic module is embedded in the actual staircase Specht square. -/
def staircaseToTensor (m : ℕ) :
    Representation.IntertwiningMap (staircaseCyclic m).toRepresentation
      ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m))) :=
  @intertwiningLiftSubrep (Equiv.Perm (Fin (staircase m).card))
    (Specht (stairTableau m) ⊗[ℂ] Specht (stairTableau m))
    (WordSpace (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0))
    _ _ _ _ _
    ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m)))
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0))
    (staircaseTensorMap m) (staircaseTensorMap_injective m)
    (staircaseCyclic m) (staircaseCyclic_le_tensorRange m)

attribute [irreducible] staircaseToTensor

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
def CyclicSaxlConjecture : Prop :=
  ∀ m, 1 ≤ m → ∀ (μ : YoungDiagram) (hμ : μ.card = (staircase m).card),
    ∃ f : Representation.IntertwiningMap (spechtRep (canonicalTableau μ hμ))
      (staircaseCyclic m).toRepresentation, f ≠ 0

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
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

lemma weighted_perm_sum {X : Type uX} [Fintype X] (t a : X → ℝ)
    (g : Equiv.Perm X) (hg : ∀ i, t (g i) = t i) :
    ∑ i, t i * a (g i) = ∑ i, t i * a i := by
  simpa only [hg] using Equiv.sum_comp g (fun i => t i * a i)

/- The strict square-moment equality used in the dominance projection.
The labels may be real; the application uses actual nonnegative integer letters. -/
theorem pair_sum_rigidity {X : Type uX} [Fintype X]
    (a t c : X → ℝ) (ω g h k : Equiv.Perm X)
    (hω : ∀ i, t (ω i) = t i) (hcomp : ∀ i, a i + a (ω i) = t i)
    (hg : ∀ i, t (g i) = t i) (hh : ∀ i, t (h i) = t i)
    (hc : ∀ i, c i = a (g i) + a (h i)) (hk : ∀ i, c i = t (k i)) : c = t := by
  have hbase : 2 * (∑ i, t i * a i) = ∑ i, t i ^ 2 := by
    have he := weighted_perm_sum t a ω hω
    have hs : (∑ i, t i * a i) + (∑ i, t i * a (ω i)) = ∑ i, t i ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_add, hcomp i, pow_two]
    linarith
  have hcross : ∑ i, t i * c i = ∑ i, t i ^ 2 := by
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib, weighted_perm_sum t a g hg, weighted_perm_sum t a h hh]
    linarith
  have hsquare : ∑ i, c i ^ 2 = ∑ i, t i ^ 2 := by
    simp only [hk]
    exact Equiv.sum_comp k (fun i => t i ^ 2)
  have hsum : ∑ i, (c i - t i) ^ 2 = 0 := by
    calc
      (∑ i, (c i - t i) ^ 2) = (∑ i, c i ^ 2) - 2 * (∑ i, t i * c i) +
          (∑ i, t i ^ 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hsquare, hcross]; ring
  funext i
  have hz : (c i - t i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j-t j))).mp hsum i
      (Finset.mem_univ i)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

end Saxl

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/

def wordOrbit {n d : ℕ} (t : Fin n → Fin d) (c : Fin n → Fin d) : Prop :=
  ∃ g : Equiv.Perm (Fin n), c = t ∘ g

lemma wordOrbit_perm {n d : ℕ} (t c : Fin n → Fin d) (g : Equiv.Perm (Fin n)) :
    wordOrbit t (c ∘ g) ↔ wordOrbit t c := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h*g⁻¹, ?_⟩
    funext i
    have he := congrFun hh (g⁻¹ i)
    simpa using he
  · rintro ⟨h, rfl⟩
    exact ⟨h*g, rfl⟩

def orbitProjection {n d : ℕ} (t : Fin n → Fin d) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n d) where
  toLinearMap := coordinateProjection (wordOrbit t)
  isIntertwining' g := by
    classical
    apply LinearMap.ext
    intro x
    ext c
    change (if wordOrbit t c then x (c ∘ g) else 0) =
      (if wordOrbit t (c ∘ g) then x (c ∘ g) else 0)
    rw [wordOrbit_perm]

def pairSumMap (n d e : ℕ) :
    Representation.IntertwiningMap (wordRep n (d*d)) (wordRep n e) :=
  wordMap (fun a c => if (finProdFinEquiv.symm a).1.val +
    (finProdFinEquiv.symm a).2.val = c.val then 1 else 0)

lemma wordTensor_single {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    wordTensor n d e (Pi.single a 1 ⊗ₜ[ℂ] Pi.single b 1) = Pi.single (mergeWords a b) 1 := by
  classical
  ext c
  rw [wordTensor_tmul]
  by_cases h : c = mergeWords a b
  · subst c; simp
  · have hh : splitLeft c ≠ a ∨ splitRight c ≠ b := by
      by_contra hn
      push Not at hn
      exact h (by rw [← merge_split c, hn.1, hn.2])
    rcases hh with hl | hr
    · simp [Pi.single_apply, h, hl]
    · simp [Pi.single_apply, h, hr]

lemma pairSumMap_single {n d e : ℕ} (a b : Fin n → Fin d) (c : Fin n → Fin e) :
    pairSumMap n d e (Pi.single (mergeWords a b) 1) c =
      if ∀ i, (a i).val + (b i).val = (c i).val then 1 else 0 := by
  classical
  rw [pairSumMap, wordMap_single]
  simp only [mergeWords, Equiv.symm_apply_apply]
  by_cases h : ∀ i, (a i).val + (b i).val = (c i).val
  · simp [h]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma altWord_inverse_sum {n d : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) :
    letI := Fintype.ofFinite H
    altWord H a = ∑ g : H, signC (g : Equiv.Perm (Fin n)) • Pi.single (a ∘ (g : Equiv.Perm (Fin n))) 1 := by
  classical
  let := Fintype.ofFinite H
  unfold altWord
  simp_rw [wordRep_single]
  apply Eq.trans ?_ (Equiv.sum_comp (Equiv.inv H) _)
  apply Finset.sum_congr rfl
  intro g hg
  congr 1
  exact (signC_inv g.val).symm


lemma paired_relation_iff {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    (∀ i, (a (g.val i)).val + (a (h.val i)).val = (t i).val) ↔ h = ω*g := by
  constructor
  · intro hh
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply ha
    apply Prod.ext
    · exact (ht h i).trans ((ht ω (g.val i)).trans (ht g i)).symm
    · apply Fin.ext
      have he := hω (g.val i)
      rw [ht g i] at he
      exact Nat.add_left_cancel ((hh i).trans he.symm)
  · rintro rfl i
    have he := hω (g.val i)
    rw [ht g i] at he
    exact he

lemma paired_term_projection {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    orbitProjection t (pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1)) =
      if h = ω*g then Pi.single t 1 else 0 := by
  classical
  ext c
  change (if wordOrbit t c then pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1) c else 0) = _
  rw [pairSumMap_single]
  simp only [Function.comp_apply]
  by_cases he : h = ω*g
  · rw [ite_eq_left he]
    have hr := (paired_relation_iff H a t ω ht ha hω g h).mpr he
    by_cases hc : c = t
    · subst c
      rw [ite_eq_left ⟨1, rfl⟩, ite_eq_left hr]
      simp
    · rw [Pi.single_eq_of_ne hc]
      have hn : ¬ ∀ i, (a (g.val i)).val + (a (h.val i)).val = (c i).val := by
        intro hh
        apply hc
        funext i
        exact Fin.ext ((hh i).symm.trans (hr i))
      simp only [hn, ite_false, ite_self]
  · rw [ite_eq_right he]
    change (if wordOrbit t c then _ else _) = (0:ℂ)
    by_cases ho : wordOrbit t c
    · rw [ite_eq_left ho]
      apply ite_eq_right
      intro hh
      obtain ⟨k,hk⟩ := ho
      have heq : (fun i => ((c i).val : ℝ)) = fun i => ((t i).val : ℝ) := by
        apply pair_sum_rigidity (fun i => ((a i).val : ℝ)) (fun i => ((t i).val : ℝ))
          (fun i => ((c i).val : ℝ)) ω.val g.val h.val k
        · intro i; rw [ht ω i]
        · intro i; exact_mod_cast hω i
        · intro i; rw [ht g i]
        · intro i; rw [ht h i]
        · intro i; exact_mod_cast (hh i).symm
        · intro i; rw [hk]; rfl
      have hct : c = t := by
        funext i
        apply Fin.ext
        exact_mod_cast congrFun heq i
      rw [hct] at hh
      exact he ((paired_relation_iff H a t ω ht ha hω g h).mp hh)
    · rw [ite_eq_right ho]

theorem repeated_alt_projection {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) :
    orbitProjection t (pairSumMap n d e (wordTensor n d d
      (altWord H a ⊗ₜ[ℂ] altWord H a))) =
      ((Nat.card H : ℂ) * signC ω.val) • Pi.single t 1 := by
  classical
  let := Fintype.ofFinite H
  rw [altWord_inverse_sum, TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.smul_tmul_smul, map_smul,
    wordTensor_single, paired_term_projection H a t ω ht ha hω]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hs (g : H) : signC g.val * signC (ω*g).val = signC ω.val := by
    simp only [Subgroup.coe_mul, map_mul]
    calc
      signC g.val * (signC ω.val * signC g.val) = signC ω.val * (signC g.val * signC g.val) := by ring
      _ = signC ω.val := by rw [signC_mul_self, mul_one]
  simp only [hs, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Fintype.card_eq_nat_card]

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

def rowReversalCell (m : ℕ) (x : (staircase m).cells) : (staircase m).cells :=
  ⟨(x.val.1, m-1-x.val.1-x.val.2), by
    have hx : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
    apply mem_staircase.mpr
    omega⟩

lemma rowReversalCell_involutive (m : ℕ) : Function.Involutive (rowReversalCell m) := by
  intro x
  have hx : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change m-1-x.val.1-(m-1-x.val.1-x.val.2) = x.val.2
    omega

def rowReversalEquiv (m : ℕ) : Equiv.Perm (staircase m).cells :=
  ⟨rowReversalCell m, rowReversalCell m, rowReversalCell_involutive m, rowReversalCell_involutive m⟩

def rowReversal (m : ℕ) : columnGroup (stairRowTableau m) :=
  ⟨((stairTableau m).trans (rowReversalEquiv m)).trans (stairTableau m).symm, by
    intro i
    change (stairTableau m ((stairTableau m).symm (rowReversalEquiv m (stairTableau m i)))).val.1 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

def repeatedTarget (m : ℕ) : Fin (staircase m).card → Fin ((staircase m).colLen 0) :=
  fun i => Fin.rev (rowWord (stairTableau m) i)

lemma repeatedTarget_fixed (m : ℕ) (g : columnGroup (stairRowTableau m)) (i) :
    repeatedTarget m (g.val i) = repeatedTarget m i := by
  apply congrArg Fin.rev
  apply Fin.ext
  exact g.property i

lemma repeated_letters_injective (m : ℕ) :
    Function.Injective (fun i => (repeatedTarget m i, rowWord (stairRowTableau m) i)) := by
  intro i j he
  apply (stairTableau m).injective
  apply Subtype.ext
  apply Prod.ext
  · have hh : Fin.rev (rowWord (stairTableau m) i) = Fin.rev (rowWord (stairTableau m) j) :=
      congrArg Prod.fst he
    exact congrArg Fin.val (Fin.rev_injective hh)
  · exact congrArg Fin.val (congrArg Prod.snd he)

lemma repeated_complement (m : ℕ) (i) :
    (rowWord (stairRowTableau m) i).val +
      (rowWord (stairRowTableau m) ((rowReversal m).val i)).val =
      (repeatedTarget m i).val := by
  have hi : (stairTableau m i).val.1 + (stairTableau m i).val.2 < m :=
    mem_staircase.mp (stairTableau m i).property
  simp only [rowWord, stairRowTableau, rowReversal, Equiv.trans_apply,
    Equiv.apply_symm_apply, repeatedTarget, Fin.val_rev, staircase_colLen, Nat.sub_zero]
  change (stairTableau m i).val.2 + (m-1-(stairTableau m i).val.1-(stairTableau m i).val.2) =
    m-((stairTableau m i).val.1+1)
  omega

theorem staircase_repeated_projection (m : ℕ) :
    orbitProjection (repeatedTarget m)
      (pairSumMap (staircase m).card ((staircase m).colLen 0) ((staircase m).colLen 0)
        (wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairRowTableau m)))) =
      ((Nat.card (columnGroup (stairRowTableau m)) : ℂ) * signC (rowReversal m).val) •
        Pi.single (repeatedTarget m) 1 := by
  exact repeated_alt_projection (columnGroup (stairRowTableau m))
    (rowWord (stairRowTableau m)) (repeatedTarget m) (rowReversal m)
    (repeatedTarget_fixed m) (repeated_letters_injective m) (repeated_complement m)

lemma staircase_repeated_projection_nonzero (m : ℕ) :
    orbitProjection (repeatedTarget m)
      (pairSumMap (staircase m).card ((staircase m).colLen 0) ((staircase m).colLen 0)
        (wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairRowTableau m)))) ≠ 0 := by
  rw [staircase_repeated_projection]
  apply smul_ne_zero
  · apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := columnGroup (stairRowTableau m))).ne'
    · intro hh
      have he := signC_mul_self (rowReversal m).val
      rw [hh, zero_mul] at he
      exact zero_ne_one he
  · intro hz
    have he := congrFun hz (repeatedTarget m)
    simp at he


theorem staircase_sign_equiv (m : ℕ) :
    Nonempty ((spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) := by
  classical
  let t := stairTableau m
  let tt := stairRowTableau m
  let y : Specht tt := ⟨polytabloid tt, mem_cyclic _ _⟩
  let R := signTwist (spechtRep tt)
  let F := orbitAverage R (rowWord t) y
  let c : ℂ := ((Finset.univ.filter
    (fun g : Equiv.Perm (Fin (staircase m).card) => rowWord t ∘ g = rowWord t)).card : ℂ)
  have hy : ∀ g : Equiv.Perm (Fin (staircase m).card), rowWord t ∘ g = rowWord t → R g y = y := by
    intro g hg
    have hc : g ∈ columnGroup tt := by
      intro i
      exact congrArg Fin.val (congrFun hg i)
    apply Subtype.ext
    change signC g • wordRep (staircase m).card ((staircase m).colLen 0) g (polytabloid tt) = polytabloid tt
    rw [polytabloid_alternating tt ⟨g, hc⟩, smul_smul, signC_mul_self, one_smul]
  have hF : F (Pi.single (rowWord t) 1) = c • y := orbitAverage_base R _ y hy
  have hc0 : c ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply Finset.card_ne_zero.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rfl
  have hm (g : columnGroup t) :
      (F (wordRep (staircase m).card ((staircase m).colLen 0) (g : Equiv.Perm (Fin (staircase m).card))
        (Pi.single (rowWord t) 1))).val (rowWord tt) = signC (g : Equiv.Perm (Fin (staircase m).card)) * c := by
    rw [F.isIntertwining, hF]
    change signC (g : Equiv.Perm (Fin (staircase m).card)) * (c *
      polytabloid tt (rowWord tt ∘ (g : Equiv.Perm (Fin (staircase m).card)))) = _
    have he : rowWord tt ∘ (g : Equiv.Perm (Fin (staircase m).card)) = rowWord tt := by
      funext i
      apply Fin.ext
      exact g.property i
    rw [he, polytabloid_rowWord, mul_one]
  let inc : Representation.IntertwiningMap (spechtRep t) (wordRep (staircase m).card ((staircase m).colLen 0)) :=
    { toLinearMap := (spechtSub t).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let f := F.comp inc
  have hf : f ≠ 0 := by
    intro hz
    have he : (F (polytabloid t)).val (rowWord tt) = 0 := by
      have he := congrArg (fun l : Representation.IntertwiningMap (spechtRep t) R =>
        (l ⟨polytabloid t, mem_cyclic _ _⟩).val (rowWord tt)) hz
      exact he
    let := Fintype.ofFinite (columnGroup t)
    have hp : (F (polytabloid t)).val (rowWord tt) =
        (Fintype.card (columnGroup t) : ℂ) * c := by
      change (F (∑ g : columnGroup t, signC (g : Equiv.Perm (Fin (staircase m).card)) •
        wordRep (staircase m).card ((staircase m).colLen 0) (g : Equiv.Perm (Fin (staircase m).card)) (Pi.single (rowWord t) 1))).val _ = _
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm]
      simp only [← mul_assoc, signC_mul_self, one_mul, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card (columnGroup t) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (mul_ne_zero hn hc0) (hp.symm.trans he)
  let := specht_irreducible t
  let := specht_irreducible tt
  let := signTwist_irreducible (spechtRep tt)
  exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩

lemma alternating_specht_line {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (y : Specht t) (hy : ∀ g : columnGroup t,
      spechtRep t g.val y = signC g.val • y) :
    ∃ c : ℂ, y.val = c • polytabloid t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  have he : columnAlt t y.val = (Fintype.card (columnGroup t) : ℂ) • y.val := by
    change (∑ g : columnGroup t, signC g.val • wordRep n (μ.colLen 0) g.val) y.val = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    have hh (g : columnGroup t) : wordRep n (μ.colLen 0) g.val y.val = signC g.val • y.val :=
      congrArg Subtype.val (hy g)
    simp only [hh, smul_smul, signC_mul_self, one_smul, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hm := columnAlt_tabloid t (spechtSub_le_tabloidSub t y.property)
  rw [he] at hm
  have hc : (Fintype.card (columnGroup t) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hx : y.val ∈ Submodule.span ℂ {polytabloid t} :=
    (Submodule.smul_mem_iff _ hc).mp hm
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨c,hc.symm⟩

def rowAverage (m : ℕ) : Specht (stairTableau m) := by
  classical
  letI := Fintype.ofFinite (columnGroup (stairRowTableau m))
  exact ∑ g : columnGroup (stairRowTableau m),
    spechtRep (stairTableau m) g.val ⟨polytabloid (stairTableau m), mem_cyclic _ _⟩

lemma rowAverage_nonzero (m : ℕ) : rowAverage m ≠ 0 := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  intro he
  have hh := congrArg (fun y : Specht (stairTableau m) => y.val (rowWord (stairTableau m))) he
  have hg (g : columnGroup (stairRowTableau m)) :
      rowWord (stairTableau m) ∘ g.val = rowWord (stairTableau m) := by
    funext i
    apply Fin.ext
    exact g.property i
  simp only [rowAverage, Submodule.coe_sum, Finset.sum_apply] at hh
  change (∑ g : columnGroup (stairRowTableau m),
    polytabloid (stairTableau m) (rowWord (stairTableau m) ∘ g.val)) = 0 at hh
  simp only [hg, polytabloid_rowWord, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hh
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero hh

lemma rowAverage_fixed (m : ℕ) (g : columnGroup (stairRowTableau m)) :
    spechtRep (stairTableau m) g.val (rowAverage m) = rowAverage m := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  unfold rowAverage
  rw [map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun h : columnGroup (stairRowTableau m) =>
    spechtRep (stairTableau m) h.val ⟨polytabloid (stairTableau m), mem_cyclic _ _⟩)

lemma signEquiv_rowAverage (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    ∃ c : ℂ, c ≠ 0 ∧ (φ (rowAverage m)).val = c • polytabloid (stairRowTableau m) := by
  have ha (g : columnGroup (stairRowTableau m)) :
      spechtRep (stairRowTableau m) g.val (φ (rowAverage m)) = signC g.val • φ (rowAverage m) := by
    have he := LinearMap.congr_fun (φ.isIntertwining' g.val) (rowAverage m)
    change φ (spechtRep (stairTableau m) g.val (rowAverage m)) =
      signC g.val • spechtRep (stairRowTableau m) g.val (φ (rowAverage m)) at he
    rw [rowAverage_fixed] at he
    have hh := congrArg (fun x => signC g.val • x) he
    simpa only [smul_smul, signC_mul_self, one_smul] using hh.symm
  obtain ⟨c,hc⟩ := alternating_specht_line (stairRowTableau m) (φ (rowAverage m)) ha
  refine ⟨c, ?_, hc⟩
  intro hz
  rw [hz, zero_smul] at hc
  apply rowAverage_nonzero m
  apply φ.injective
  exact (Subtype.ext hc).trans (map_zero φ).symm

def signTwistMap {n : ℕ} {X : Type uX} {Y : Type uY} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X} {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    (f : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap (signTwist ρ) (signTwist σ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext x
    change f (signC g • ρ g x) = signC g • σ g (f x)
    rw [map_smul, f.isIntertwining]

/- A sign intertwiner in the second factor twists the diagonal product. -/
def tensorAnti {n : ℕ} {X : Type uX} {Y : Type uY} {Z : Type uZ} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y} {τ : Representation ℂ (Equiv.Perm (Fin n)) Z}
    (f : Representation.IntertwiningMap σ (signTwist τ)) :
    Representation.IntertwiningMap (signTwist (ρ.tprod σ)) (ρ.tprod τ) where
  toLinearMap := TensorProduct.map LinearMap.id f.toLinearMap
  isIntertwining' g := by
    ext x y
    change TensorProduct.map LinearMap.id f.toLinearMap
      (signC g • (ρ g x ⊗ₜ[ℂ] σ g y)) = ρ g x ⊗ₜ[ℂ] τ g (f y)
    rw [map_smul, TensorProduct.map_tmul]
    change signC g • (ρ g x ⊗ₜ[ℂ] f (σ g y)) = _
    rw [f.isIntertwining]
    change signC g • (ρ g x ⊗ₜ[ℂ] (signC g • τ g (f y))) = _
    rw [TensorProduct.tmul_smul, smul_smul, signC_mul_self, one_smul]

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma subrepProject_subtype {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) (x : S) :
    subrepProject S hS x.val = x := by
  change (subrepSelfDual S hS).symm (subrepSelfDual S hS x) = x
  exact (subrepSelfDual S hS).symm_apply_apply x

def wordTensorEquiv (n d e : ℕ) :
    ((wordRep n d).tprod (wordRep n e)).Equiv (wordRep n (d*e)) where
  toLinearEquiv := wordTensor n d e
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    exact wordTensor_equivariant g z

def ambientSignMap (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Representation.IntertwiningMap (wordRep (staircase m).card ((staircase m).colLen 0))
      (signTwist (wordRep (staircase m).card ((staircase m).colLen 0))) :=
  (signTwistMap (spechtInclusion (stairRowTableau m))).comp
    (φ.toIntertwiningMap.comp (subrepProject (spechtSub (stairTableau m))
      (fun _ hx => cyclic_star _ (polytabloid_real _) hx)))

lemma ambientSignMap_subtype (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m))))
    (x : Specht (stairTableau m)) : ambientSignMap m φ x.val = (φ x).val := by
  change (φ (subrepProject (spechtSub (stairTableau m)) _ x.val)).val = _
  exact congrArg (fun y : Specht (stairTableau m) => (φ y).val)
    (subrepProject_subtype (spechtSub (stairTableau m)) _ x)

def pairAntiMap (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Representation.IntertwiningMap
      (signTwist (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)))
      (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)) :=
  (wordTensorEquiv _ _ _).toIntertwiningMap.comp
    ((tensorAnti (wordRep _ _) (ambientSignMap m φ)).comp
      (signTwistMap (wordTensorEquiv _ _ _).symm.toIntertwiningMap))

lemma pairAntiMap_tensor (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m))))
    (x y : WordSpace (staircase m).card ((staircase m).colLen 0)) :
    pairAntiMap m φ (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)) =
      wordTensor _ _ _ (x ⊗ₜ[ℂ] ambientSignMap m φ y) := by
  change wordTensor _ _ _ (TensorProduct.map LinearMap.id (ambientSignMap m φ).toLinearMap
    ((wordTensor _ _ _).symm (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

lemma signed_average_staircase (m : ℕ) :
    letI := Fintype.ofFinite (columnGroup (stairRowTableau m))
    ∑ g : columnGroup (stairRowTableau m), signC g.val •
      wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0) g.val (staircaseWord m) =
    wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] (rowAverage m).val) := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  change _ = wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ]
    (∑ g : columnGroup (stairRowTableau m),
      spechtRep (stairTableau m) g.val ⟨polytabloid (stairTableau m), mem_cyclic _ _⟩).val)
  rw [Submodule.coe_sum, TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  change signC g.val • wordRep _ _ g.val (wordTensor _ _ _
    (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairTableau m))) = _
  rw [← wordTensor_equivariant]
  change signC g.val • wordTensor _ _ _
    (wordRep _ _ g.val (polytabloid (stairRowTableau m)) ⊗ₜ[ℂ]
      wordRep _ _ g.val (polytabloid (stairTableau m))) = _
  rw [polytabloid_alternating _ g, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
    smul_smul, signC_mul_self, one_smul]
  rfl

def dominatedQuotient (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Representation.IntertwiningMap (signTwist (staircaseCyclic m).toRepresentation)
      (wordRep (staircase m).card ((staircase m).colLen 0)) :=
  (orbitProjection (repeatedTarget m)).comp ((pairSumMap _ _ _).comp
    ((pairAntiMap m φ).comp (signTwistMap
      { toLinearMap := (staircaseCyclic m).toSubmodule.subtype
        isIntertwining' := fun _ => rfl })))

/- The exact staircase permutation generator occurs in the image of the
sign-twisted cyclic staircase module, with no Young-rule input. -/
theorem repeatedTarget_in_quotient (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Pi.single (repeatedTarget m) (1:ℂ) ∈ (dominatedQuotient m φ).range := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  obtain ⟨c,hc,hφ⟩ := signEquiv_rowAverage m φ
  let x : (staircaseCyclic m).toSubmodule := ∑ g : columnGroup (stairRowTableau m), signC g.val •
    (staircaseCyclic m).toRepresentation g.val ⟨staircaseWord m, mem_cyclic _ _⟩
  have hx : x.val = wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] (rowAverage m).val) := by
    change (∑ g : columnGroup (stairRowTableau m), signC g.val •
      (staircaseCyclic m).toRepresentation g.val ⟨staircaseWord m, mem_cyclic _ _⟩).val = _
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    exact signed_average_staircase m
  let q : ℂ := (Nat.card (columnGroup (stairRowTableau m)) : ℂ) * signC (rowReversal m).val
  have hq : q ≠ 0 := by
    apply mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.card_pos (α := columnGroup (stairRowTableau m))).ne')
    intro hz
    have hh := signC_mul_self (rowReversal m).val
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have hF : dominatedQuotient m φ x = (c*q) • Pi.single (repeatedTarget m) (1:ℂ) := by
    change orbitProjection (repeatedTarget m) (pairSumMap _ _ _ (pairAntiMap m φ x.val)) = _
    rw [hx, pairAntiMap_tensor, ambientSignMap_subtype, hφ,
      TensorProduct.tmul_smul, map_smul, map_smul, map_smul, staircase_repeated_projection, smul_smul]
  have hm : (c*q) • Pi.single (repeatedTarget m) (1:ℂ) ∈ (dominatedQuotient m φ).range :=
    ⟨x,hF⟩
  exact (Submodule.smul_mem_iff _ (mul_ne_zero hc hq)).mp hm

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


namespace Saxl

lemma transpose_card (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  change ((Equiv.prodComm ℕ ℕ).finsetCongr μ.cells).card = μ.cells.card
  simp only [Equiv.finsetCongr_apply, Finset.card_map]

def colTruncate (μ : YoungDiagram) (k : ℕ) := (rowTruncate μ.transpose k).transpose

lemma colTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (colTruncate μ k).rowLen i = min k (μ.rowLen i) := by
  have hh : ∀ j, j < (colTruncate μ k).rowLen i ↔ j < min k (μ.rowLen i) := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    change (i,j) ∈ (rowTruncate μ.transpose k).transpose ↔ _
    rw [YoungDiagram.mem_transpose]
    change (j,i) ∈ rowTruncate μ.transpose k ↔ _
    rw [mem_rowTruncate, YoungDiagram.mem_transpose]
    simp only [Prod.swap_prod_mk, YoungDiagram.mem_iff_lt_rowLen, lt_min_iff]
    omega
  have h₁ := hh ((colTruncate μ k).rowLen i)
  have h₂ := hh (min k (μ.rowLen i))
  omega

lemma colTruncate_height (μ : YoungDiagram) (k : ℕ) :
    (colTruncate μ k).colLen 0 ≤ μ.colLen 0 := by
  by_contra h
  have hm : (μ.colLen 0,0) ∈ colTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hm
  rw [colTruncate_rowLen, rowLen_zero_of_height_le μ le_rfl] at hr
  simp at hr

lemma sum_range_if_lt (f : ℕ → ℕ) {r H : ℕ} (hr : r ≤ H) :
    (∑ i ∈ Finset.range H, if i < r then f i else 0) = ∑ i ∈ Finset.range r, f i := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma corner_inequality (μ : YoungDiagram) (k r : ℕ) :
    rowPrefix μ.transpose k + rowPrefix μ r ≤ μ.card + r*k := by
  let H := max (μ.colLen 0) r
  have hh : μ.colLen 0 ≤ H := Nat.le_max_left _ _
  have hr : r ≤ H := Nat.le_max_right _ _
  have hm : rowPrefix μ.transpose k = ∑ i ∈ Finset.range H, min k (μ.rowLen i) := by
    rw [← rowTruncate_card, ← transpose_card (rowTruncate μ.transpose k)]
    change (colTruncate μ k).card = _
    rw [← rowPrefix_eq_card _ ((colTruncate_height μ k).trans hh)]
    exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)
  rw [hm, ← rowPrefix_eq_card μ hh]
  change _ + (∑ i ∈ Finset.range r, μ.rowLen i) ≤ (∑ i ∈ Finset.range H, μ.rowLen i) + r*k
  have hconst : (∑ i ∈ Finset.range r, k) = r*k := by simp
  rw [← hconst, ← sum_range_if_lt μ.rowLen hr, ← sum_range_if_lt (fun _ => k) hr,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> omega

lemma corner_equality (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ.transpose k + rowPrefix μ (μ.colLen k) = μ.card + μ.colLen k*k := by
  let r := μ.colLen k
  let H := μ.colLen 0
  have hr : r ≤ H := μ.colLen_anti 0 k (Nat.zero_le _)
  have hm : rowPrefix μ.transpose k = ∑ i ∈ Finset.range H, min k (μ.rowLen i) := by
    rw [← rowTruncate_card, ← transpose_card (rowTruncate μ.transpose k)]
    change (colTruncate μ k).card = _
    rw [← rowPrefix_eq_card _ (colTruncate_height μ k)]
    exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)
  change rowPrefix μ.transpose k + rowPrefix μ r = μ.card + r*k
  rw [hm, ← rowPrefix_eq_card μ (le_refl H)]
  change _ + (∑ i ∈ Finset.range r, μ.rowLen i) = (∑ i ∈ Finset.range H, μ.rowLen i) + r*k
  have hconst : (∑ i ∈ Finset.range r, k) = r*k := by simp
  rw [← hconst, ← sum_range_if_lt μ.rowLen hr, ← sum_range_if_lt (fun _ => k) hr,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have he : i < r ↔ k < μ.rowLen i := by
    exact YoungDiagram.mem_iff_lt_colLen.symm.trans YoungDiagram.mem_iff_lt_rowLen
  split_ifs with h
  · have hh := he.mp h
    omega
  · have hh := not_congr he |>.mp h
    omega

/- Ordinary conjugation reverses dominance, including empty diagrams. -/
theorem dominates_transpose {μ ν : YoungDiagram} (hc : μ.card = ν.card)
    (h : Dominates μ ν) : Dominates ν.transpose μ.transpose := by
  intro k
  have h₁ := corner_inequality μ k (ν.colLen k)
  have h₂ := corner_equality ν k
  have h₃ := h (ν.colLen k)
  omega

open scoped MonoidAlgebra

end Saxl

namespace Saxl

lemma rowWord_content {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (j : Fin (μ.colLen 0)) :
    (Finset.univ.filter (fun i => rowWord t i = j)).card = μ.rowLen j := by
  classical
  let e : {i // rowWord t i = j} ≃ Fin (μ.rowLen j) :=
    { toFun := fun i => ⟨(t i.val).val.2, by
        have hh := YoungDiagram.mem_iff_lt_rowLen.mp (t i.val).property
        have hj := congrArg Fin.val i.property
        change (t i.val).val.1 = j.val at hj
        simpa only [hj] using hh⟩
      invFun := fun k => ⟨t.symm ⟨(j.val,k.val), YoungDiagram.mem_iff_lt_rowLen.mpr k.isLt⟩,
        by apply Fin.ext; change (t (t.symm _)).val.1 = _; simp only [Equiv.apply_symm_apply]⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply t.injective
        simp only [Equiv.apply_symm_apply]
        apply Subtype.ext
        apply Prod.ext
        · exact (congrArg Fin.val i.property).symm
        · rfl
      right_inv := by intro k; apply Fin.ext; simp only [Equiv.apply_symm_apply] }
  simpa only [Fintype.card_subtype, Fintype.card_fin] using Fintype.card_congr e

@[simp] lemma staircase_transpose (m : ℕ) : (staircase m).transpose = staircase m := by
  apply YoungDiagram.ext
  apply Finset.ext
  intro x
  rcases x with ⟨i,j⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Prod.swap_prod_mk, mem_staircase]
  omega

def signCancelMap {n : ℕ} {X : Type uX} {Y : Type uY} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X} {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    (f : Representation.IntertwiningMap (signTwist ρ) σ) :
    Representation.IntertwiningMap ρ (signTwist σ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext x
    change f (ρ g x) = signC g • σ g (f x)
    have hh := LinearMap.congr_fun (f.isIntertwining' g) x
    change f (signC g • ρ g x) = σ g (f x) at hh
    have he := congrArg (fun y => signC g • y) hh
    rw [map_smul, smul_smul, signC_mul_self, one_smul] at he
    exact he

theorem dominated_support (m : ℕ) (_hm : 1 ≤ m) (μ : YoungDiagram)
    (t : Tableau (staircase m).card μ) (hμ : Dominates (staircase m) μ) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (staircaseCyclic m).toRepresentation, f ≠ 0 := by
  classical
  have hc : μ.card = (staircase m).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr t).symm
  have ht : μ.transpose.card = (staircase m).card := by rw [transpose_card, hc]
  have hd : Dominates μ.transpose (staircase m) := by
    simpa only [staircase_transpose] using dominates_transpose hc.symm hμ
  have hw (j : Fin ((staircase m).colLen 0)) :
      (Finset.univ.filter (fun i => repeatedTarget m i = Fin.rev j)).card = (staircase m).rowLen j := by
    simpa only [repeatedTarget, Fin.rev_inj] using rowWord_content (stairTableau m) j
  obtain ⟨F,hF⟩ := young_orbit_map (staircase m) μ.transpose (transposeTableau t)
    ht hd (repeatedTarget m) Fin.revPerm hw
  obtain ⟨φ⟩ := staircase_sign_equiv m
  let Q := F.comp (dominatedQuotient m φ)
  have hQ : Q ≠ 0 := by
    obtain ⟨x,hx⟩ := repeatedTarget_in_quotient m φ
    intro hz
    apply hF
    have hh := congrArg (fun l => l x) hz
    change F (dominatedQuotient m φ x) = 0 at hh
    change dominatedQuotient m φ x = Pi.single (repeatedTarget m) 1 at hx
    rwa [hx] at hh
  obtain ⟨E⟩ := specht_sign_transpose t
  let R := E.symm.toIntertwiningMap.comp (signCancelMap Q)
  have hR : R ≠ 0 := by
    intro hz
    apply hQ
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun l => l x) hz
    change E.symm (Q x) = 0 at hh
    exact E.symm.injective (hh.trans (map_zero _).symm)
  let := specht_irreducible t
  have hRs : Function.Surjective R :=
    (Representation.IsIrreducible.surjective_or_eq_zero R).resolve_right hR
  obtain ⟨f,hf⟩ := intertwining_lift_surjective R hRs (Representation.IntertwiningMap.id (spechtRep t))
  refine ⟨f, ?_⟩
  intro hz
  have hzero : (Representation.IntertwiningMap.id (spechtRep t)) = 0 := by
    rw [← hf, hz]
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact map_zero R
  have he := congrArg (fun l : Representation.IntertwiningMap (spechtRep t) (spechtRep t) =>
    l ⟨polytabloid t, mem_cyclic _ _⟩) hzero
  exact polytabloid_ne_zero t (congrArg Subtype.val he)

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
inductive StripChain : ℕ → YoungDiagram → YoungDiagram → Prop
  | nil (μ) : StripChain 0 μ μ
  | snoc {q ν η μ} : StripChain q ν η → HorizontalStrip η μ → η ≠ μ → StripChain (q+1) ν μ


lemma stripRemove_full_prefix (μ : YoungDiagram) (q : ℕ) :
    rowPrefix (stripRemove μ (μ.rowLen 0)) q + μ.rowLen 0 = rowPrefix μ (q+1) := by
  have hh := stripRemove_prefix μ (μ.rowLen 0) q
  rw [min_self, min_eq_right (μ.rowLen_anti 0 q (Nat.zero_le _))] at hh
  exact hh.trans (rowPrefix_succ μ q).symm

/- Sweeps remove any prescribed number within the first q-row capacity. -/
theorem stripChain_of_capacity (q t : ℕ) (μ : YoungDiagram)
    (ht : t ≤ rowPrefix μ q) :
    ∃ k ≤ q, ∃ ν, ν.card + t = μ.card ∧ StripChain k ν μ := by
  induction q generalizing t μ with
  | zero =>
    have hz : t = 0 := by simpa [rowPrefix] using ht
    exact ⟨0, le_rfl, μ, by omega, StripChain.nil μ⟩
  | succ q ih =>
    by_cases hz : t = 0
    · exact ⟨0, Nat.zero_le _, μ, by omega, StripChain.nil μ⟩
    by_cases hb : t ≤ μ.rowLen 0
    · let ν := stripRemove μ t
      have hc : ν.card + t = μ.card := by
        simpa only [ν, min_eq_left hb] using stripRemove_card μ t
      have hn : ν ≠ μ := by intro he; rw [he] at hc; omega
      exact ⟨1, by omega, ν, hc,
        StripChain.snoc (StripChain.nil ν) (stripRemove_horizontal μ t) hn⟩
    · let η := stripRemove μ (μ.rowLen 0)
      have hp : rowPrefix η q + μ.rowLen 0 = rowPrefix μ (q+1) :=
        stripRemove_full_prefix μ q
      have hcap : t - μ.rowLen 0 ≤ rowPrefix η q := by omega
      obtain ⟨k, hk, ν, hc, hchain⟩ := ih (t-μ.rowLen 0) η hcap
      have hec : η.card + μ.rowLen 0 = μ.card := by
        simpa only [η, min_self] using stripRemove_card μ (μ.rowLen 0)
      have hpos : 0 < μ.rowLen 0 := by
        by_contra h
        have hz0 : μ.rowLen 0 = 0 := by omega
        have hp0 : rowPrefix μ (q+1) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hh := μ.rowLen_anti 0 i (Nat.zero_le _)
          omega
        omega
      have hn : η ≠ μ := by intro he; rw [he] at hec; omega
      refine ⟨k+1, by omega, ν, ?_, StripChain.snoc hchain (stripRemove_horizontal μ _) hn⟩
      omega

lemma rowPrefix_mean (μ : YoungDiagram) {q k : ℕ} (hqk : q ≤ k) :
    q * rowPrefix μ k ≤ k * rowPrefix μ q := by
  have hlow : q * μ.rowLen q ≤ rowPrefix μ q := by
    calc
      q * μ.rowLen q = ∑ i ∈ Finset.range q, μ.rowLen q := by simp
      _ ≤ rowPrefix μ q := Finset.sum_le_sum (fun i hi =>
        μ.rowLen_anti i q (Nat.le_of_lt (Finset.mem_range.mp hi)))
  have he : rowPrefix μ k = rowPrefix μ q +
      ∑ i ∈ Finset.range (k-q), μ.rowLen (q+i) := by
    simp only [rowPrefix]
    rw [← Finset.sum_range_add]
    congr 2
    omega
  have htail : (∑ i ∈ Finset.range (k-q), μ.rowLen (q+i)) ≤ (k-q)*μ.rowLen q := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k-q), μ.rowLen q :=
        Finset.sum_le_sum (fun i hi => μ.rowLen_anti q (q+i) (by omega))
      _ = _ := by simp
  have hm := Nat.mul_le_mul_left (k-q) hlow
  have hs := Nat.mul_le_mul_left q htail
  rw [he]
  have hsum : q + (k-q) = k := by omega
  nlinarith

@[simp] lemma staircase_rowLen (m i : ℕ) : (staircase m).rowLen i = m-i := by
  have hh : ∀ j, j < (staircase m).rowLen i ↔ j < m-i := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_staircase]
    omega
  have h₁ := hh ((staircase m).rowLen i)
  have h₂ := hh (m-i)
  omega

lemma staircase_prefix_double (m k : ℕ) (hk : k ≤ m) :
    2 * rowPrefix (staircase m) k = k * (2*m+1-k) := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    rw [rowPrefix_succ, staircase_rowLen]
    have hi := ih (by omega)
    have hs : k + (m-k) = m := by omega
    have ht : k + (2*m+1-k) = 2*m+1 := by omega
    have ht' : (k+1) + (2*m+1-(k+1)) = 2*m+1 := by omega
    nlinarith

/- The exact capacity alternative used by the main induction. -/
lemma strip_reduction_capacity (m : ℕ) (hm : 2 ≤ m) (μ : YoungDiagram)
    (hμ : μ.card = (staircase m).card) (hdom : ¬ Dominates (staircase m) μ)
    (hfirst : μ.rowLen 0 < m) : 5 ≤ m ∧ 2*m-1 ≤ rowPrefix μ 4 := by
  obtain ⟨k, hk⟩ : ∃ k, rowPrefix (staircase m) k < rowPrefix μ k := by
    simpa only [Dominates, not_forall, not_le] using hdom
  have hkm : k < m := by
    by_contra hh
    have hc : (staircase m).colLen 0 ≤ k := by simp; omega
    rw [rowPrefix_eq_card _ hc] at hk
    have hle := rowPrefix_le_card μ k
    omega
  have hbound : rowPrefix μ k ≤ k * (m-1) := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, (m-1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := μ.rowLen_anti 0 i (Nat.zero_le _)
        omega
      _ = _ := by simp
  have hstair := staircase_prefix_double m k (by omega)
  have hk4 : 4 ≤ k := by
    have hm1 : m = (m-1)+1 := by omega
    by_contra hh
    interval_cases k <;> omega
  have hmean := rowPrefix_mean μ hk4
  have hpos : 0 < k := by omega
  have hsum : k + (2*m+1-k) = 2*m+1 := by omega
  constructor
  · omega
  · have ha : 4*(2*m+1-k) < 2*rowPrefix μ 4 := by
      nlinarith
    have hb : 2*m-1 ≤ 2*(2*m+1-k) := by omega
    omega

theorem strip_reduction (m : ℕ) (hm : 2 ≤ m) (μ : YoungDiagram)
    (hμ : μ.card = (staircase m).card) (hdom : ¬ Dominates (staircase m) μ) :
    (∃ ν, ν.card = (staircase (m-1)).card ∧ HorizontalStrip ν μ) ∨
    (5 ≤ m ∧ ∃ q ≤ 4, ∃ ν, ν.card = (staircase (m-2)).card ∧ StripChain q ν μ) := by
  by_cases hfirst : m ≤ μ.rowLen 0
  · left
    let ν := stripRemove μ m
    have hc : ν.card + m = μ.card := by
      simpa only [ν, min_eq_left hfirst] using stripRemove_card μ m
    have hs : (staircase m).card = (staircase (m-1)).card + m := by
      have hh := staircase_card_succ (m-1)
      have he : m-1+1 = m := by omega
      simpa only [he] using hh
    exact ⟨ν, by omega, stripRemove_horizontal μ m⟩
  · right
    obtain ⟨hm5, hcap⟩ := strip_reduction_capacity m hm μ hμ hdom (by omega)
    obtain ⟨q, hq, ν, hc, hs⟩ := stripChain_of_capacity 4 (2*m-1) μ hcap
    refine ⟨hm5, q, hq, ν, ?_, hs⟩
    have hc₁ := staircase_card_double m
    have hc₂ := staircase_card_double (m-2)
    have hh : m = (m-2)+2 := by omega
    have ht : 2*m-1+1 = 2*m := by omega
    nlinarith

end Saxl

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped TensorProduct


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
theorem saxl_conjecture_oai : SaxlConjecture := saxl_of_cyclic_support cyclic_saxl_conjecture



theorem cyclic_saxl : CyclicSaxlConjecture := cyclic_saxl_conjecture

/- Specht classification implies that every finite-dimensional irreducible
complex representation embeds in the staircase tensor square. -/
theorem saxl_contains_every_irreducible (m : ℕ) (hm : 1 ≤ m)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (staircase m).card)) V)
    [Representation.IsIrreducible ρ] :
    ∃ F : Representation.IntertwiningMap ρ
      ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m))),
      Function.Injective F := by
  obtain ⟨p,⟨e⟩⟩ := irreducible_equiv_specht ρ
  obtain ⟨f,hf⟩ := full_cyclic_support m hm (partitionDiagram p) (partitionTableau p)
  let := specht_irreducible (partitionTableau p)
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  exact ⟨((staircaseToTensor m).comp f).comp e.toIntertwiningMap,
    (staircaseToTensor_injective m).comp (hi.comp e.injective)⟩

/- The positive-multiplicity conclusion with the literal
triangular degree, rather than the definitionally convenient cell count. -/
theorem saxl_kronecker_pos (m : ℕ) (hm : 1 ≤ m) (μ : YoungDiagram)
    (hμ : μ.card = m * (m + 1) / 2) :
    0 < kronecker (canonicalTableau (staircase m) (staircase_card m))
      (canonicalTableau (staircase m) (staircase_card m)) (canonicalTableau μ hμ) := by
  have H : ∀ (n : ℕ) (hn : (staircase m).card = n) (hnu : μ.card = n),
      0 < kronecker (canonicalTableau (staircase m) hn)
        (canonicalTableau (staircase m) hn) (canonicalTableau μ hnu) := by
    intro n hn hnu
    subst n
    exact saxl_conjecture_oai m hm μ hnu
  exact H _ (staircase_card m) hμ

end Saxl

end

end OAI
end
end

open scoped TensorProduct in
theorem solution : type_of% @OAI.Saxl.saxl_conjecture_oai := @OAI.Saxl.saxl_conjecture_oai
