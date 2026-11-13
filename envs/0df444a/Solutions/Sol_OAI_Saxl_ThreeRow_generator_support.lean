-- Prove2me | solution 1 for OAI.Saxl.ThreeRow.generator_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:08:12.98304+00:00
-- url     : https://prove2.me/submissions/4398642c-8b72-4a7b-82ff-d8328e6c4c9f

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021

section
-- module Solutions.OAIQ259_US.Saxl_SpechtDuality
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The ordinary bilinear coordinate pairing restricted to any invariant word subspace. -/

lemma subrepProject_pair {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule)
    (x : WordSpace n d) (y : S.toSubmodule) :
    dotProduct (subrepProject S hS x).val y.val = dotProduct x y.val := by
  have hh := (subrepSelfDual S hS).apply_symm_apply (subrepPairFromAmbient S x)
  exact congrArg (fun f : Module.Dual ℂ S.toSubmodule => f y) hh

/- A tensor power of a single letter-linear map, in ordinary word coordinates. -/
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

section
-- module Solutions.OAIQ259_US.Saxl_HighProjection
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/


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

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PositionSplit
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.joinPositions_parts _root_.OAI.Saxl.leftWord_join _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.rightWord_join _root_.OAI.Saxl.sumPerm_mul _root_.OAI.Saxl.sumPerm_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl
/- The genuine product position permutation under a disjoint-set enumeration. -/

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
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

/- Explicit finite-group induction on a linear map. -/

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

end Saxl

namespace Saxl

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

lemma cyclic_action_eq {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (g : G) : cyclic ρ (ρ g v) = cyclic ρ v := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr ((cyclic ρ v).apply_mem_toSubmodule g (mem_cyclic ρ v))
  · apply (cyclic_le _ _ _).mpr
    have hh := (cyclic ρ (ρ g v)).apply_mem_toSubmodule g⁻¹ (mem_cyclic ρ (ρ g v))
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at hh
    exact hh

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

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

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SpechtClassification
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.tableauInclusion_cell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV uG

namespace Saxl

/- Rows enumerate exactly the actual cells, including the empty diagram. -/



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

section
-- module Solutions.OAIQ259_US.Saxl_SupportSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uR uX uY uG uV

namespace Saxl

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

section
-- module Solutions.OAIQ259_US.Saxl_BandOrbit
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

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

section
-- module Solutions.OAIQ259_US.Saxl_BandGlue
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- Apply a band intertwiner to every scalar high-coordinate of a colored
strip orbit map. This is the concrete tensor product of the two maps. -/

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

section
-- module Solutions.OAIQ259_US.Saxl_PieriRestriction
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A horizontal strip removes at most one cell in each column. -/

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

section
-- module Solutions.OAIQ259_US.Saxl_StripExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

section
-- module Solutions.OAIQ259_US.Saxl_SizedStrips
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl



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

section
-- module Solutions.OAIQ259_US.Saxl_StripSupport
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

section
-- module Solutions.OAIQ259_US.Saxl_YoungRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Horizontal-strip chains recording the exact ordered strip sizes. -/

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

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

lemma SizedStripChain.of_horizontal {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    SizedStripChain [μ.card-ν.card] ν μ := by
  have hc : ν.card ≤ μ.card := Finset.card_le_card hs.1
  exact SizedStripChain.snoc (SizedStripChain.nil ν) hs (Nat.add_sub_of_le hc)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SymmetricPairs
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma symmetricPairs_real {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) :
    star (symmetricPairs e d) = symmetricPairs e d := by
  ext w
  simp only [Pi.star_apply, symmetricPairs]
  split_ifs <;> simp

lemma symmetricPairs_contraction {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (x y : WordSpace m d) :
    dotProduct (positionProduct e x y) (symmetricPairs e d) = dotProduct x y := by
  classical
  unfold dotProduct
  calc
    _ = ∑ p : (Fin m → Fin d) × (Fin m → Fin d),
        x p.1 * y p.2 * (if p.1 = p.2 then 1 else 0) := by
      apply Fintype.sum_equiv (positionWordsEquiv e)
      intro w
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp

lemma real_self_pair_ne_zero {n d : ℕ} (x : WordSpace n d)
    (hr : star x = x) (hx : x ≠ 0) : dotProduct x x ≠ 0 := by
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  intro he
  apply hx
  exact dotProduct_self_star_eq_zero.mp (by simpa only [hr] using he)

lemma pairedTableau_left {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) (i : Fin m) :
    (pairedTableau μ he e s (e.symm (Sum.inl i))).val =
      ((s i).val.1, 2*(s i).val.2) := by
  simp [pairedTableau, pairedCells]

lemma pairedTableau_right {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) (i : Fin m) :
    (pairedTableau μ he e s (e.symm (Sum.inr i))).val =
      ((s i).val.1, 2*(s i).val.2+1) := by
  simp [pairedTableau, pairedCells]

lemma pairedTableau_group_sector {n m : ℕ} (μ : YoungDiagram)
    (he : ∀ i, Even (μ.rowLen i)) (e : Fin n ≃ Fin m ⊕ Fin m)
    (s : Tableau m (halfRows μ)) :
    columnGroup (pairedTableau μ he e s) ≤ sectorGroup (fun i => (e i).isLeft = true) := by
  intro g hg i
  have hc := hg i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  obtain ⟨k,hk⟩ := e.symm.surjective (g (e.symm j))
  rw [← hk] at hc ⊢
  cases j <;> cases k <;>
    simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, Sum.isLeft_inr] at *
  · rw [pairedTableau_left, pairedTableau_right] at hc
    dsimp only at hc
    omega
  · rw [pairedTableau_left, pairedTableau_right] at hc
    dsimp only at hc
    omega

lemma pairedTableau_factor {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) :
    polytabloid (pairedTableau μ he e s) = positionProduct e
      (letterLift (Fin.cast (halfRows_height μ he)) (polytabloid s))
      (letterLift (Fin.cast (halfRows_height μ he)) (polytabloid s)) := by
  let t := pairedTableau μ he e s
  let f : Fin n → ℕ := fun i => (t i).val.2
  have hn : columnGroup t = fiberGroup f := rfl
  have hg : columnGroup t = fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true) := by
    rw [← hn]
    exact (inf_eq_left.mpr (pairedTableau_group_sector μ he e s)).symm
  have hl : fiberGroup (fun i => f (e.symm (Sum.inl i))) = columnGroup s := by
    apply Subgroup.ext
    intro g
    change (∀ i, (t (e.symm (Sum.inl (g i)))).val.2 =
      (t (e.symm (Sum.inl i))).val.2) ↔ ∀ i, (s (g i)).val.2 = (s i).val.2
    simp only [t, pairedTableau_left, Nat.mul_right_inj (by decide : 2 ≠ 0)]
  have hr : fiberGroup (fun i => f (e.symm (Sum.inr i))) = columnGroup s := by
    apply Subgroup.ext
    intro g
    change (∀ i, (t (e.symm (Sum.inr (g i)))).val.2 =
      (t (e.symm (Sum.inr i))).val.2) ↔ ∀ i, (s (g i)).val.2 = (s i).val.2
    simp only [t, pairedTableau_right, Nat.add_right_cancel_iff,
      Nat.mul_right_inj (by decide : 2 ≠ 0)]
  have hw₁ : leftWord e (rowWord t) = Fin.cast (halfRows_height μ he) ∘ rowWord s := by
    funext i
    apply Fin.ext
    change (t (e.symm (Sum.inl i))).val.1 = (s i).val.1
    rw [pairedTableau_left]
  have hw₂ : rightWord e (rowWord t) = Fin.cast (halfRows_height μ he) ∘ rowWord s := by
    funext i
    apply Fin.ext
    change (t (e.symm (Sum.inr i))).val.1 = (s i).val.1
    rw [pairedTableau_right]
  change polytabloid t = _
  rw [polytabloid_eq_altWord, hg, altWord_fiber_split, hl, hr, hw₁, hw₂,
    ← letterLift_altWord, ← polytabloid_eq_altWord]

lemma letterLift_real {n a b : ℕ} (φ : Fin a → Fin b) (x : WordSpace n a)
    (hr : star x = x) : star (letterLift φ x) = letterLift φ x := by
  classical
  funext w
  change star (∑ c, x c * ∏ i, if φ (c i) = w i then (1 : ℂ) else 0) = _
  simp only [star_sum, star_mul, star_prod, apply_ite, star_one, star_zero]
  have hx (c) : star (x c) = x c := congrFun hr c
  simp_rw [hx]
  simp only [letterLift, wordMap, mul_comm]
  rfl

lemma letterLift_pair {n a b : ℕ} (φ : Fin a → Fin b)
    (x : WordSpace n a) (y : WordSpace n b) :
    dotProduct (letterLift φ x) y = dotProduct x (fun w => y (φ ∘ w)) := by
  classical
  have hx : x = ∑ w, x w • Pi.single w (1 : ℂ) := by
    funext w
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_smul, letterLift_single]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  funext w
  simp [Pi.single_apply]

lemma letterLift_symmetricPairs_pair {n m a b : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (φ : Fin a → Fin b)
    (hφ : Function.Injective φ) (x : WordSpace n a) :
    dotProduct (letterLift φ x) (symmetricPairs e b) =
      dotProduct x (symmetricPairs e a) := by
  rw [letterLift_pair]
  congr 1
  funext w
  have hh : leftWord e (φ ∘ w) = rightWord e (φ ∘ w) ↔
      leftWord e w = rightWord e w := by
    constructor
    · intro h
      funext i
      exact hφ (congrFun h i)
    · intro h
      funext i
      exact congrArg φ (congrFun h i)
  simp only [symmetricPairs, hh]

lemma pairedTableau_contraction {n m : ℕ} (μ : YoungDiagram)
    (he : ∀ i, Even (μ.rowLen i)) (e : Fin n ≃ Fin m ⊕ Fin m)
    (s : Tableau m (halfRows μ)) :
    dotProduct (polytabloid (pairedTableau μ he e s))
      (symmetricPairs e (μ.colLen 0)) ≠ 0 := by
  rw [pairedTableau_factor, symmetricPairs_contraction]
  apply real_self_pair_ne_zero
  · exact letterLift_real _ _ (polytabloid_real s)
  · intro hz
    apply polytabloid_ne_zero s
    exact letterLift_injective _ (Fin.cast_injective _) (hz.trans (map_zero _).symm)

lemma halfRows_card (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i)) :
    2 * (halfRows μ).card = μ.card := by
  have hc := Fintype.card_congr (pairedCells μ he)
  simpa only [Fintype.card_sum, Fintype.card_coe, ← two_mul] using hc

theorem even_rows_symmetricPairs_support {n m d : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (symmetricPairs e d)).toRepresentation, F ≠ 0 := by
  have hn : μ.card = n := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr t).symm
  have hnm : n = 2*m := by
    simpa only [Fintype.card_fin, Fintype.card_sum, ← two_mul] using Fintype.card_congr e
  have hm : (halfRows μ).card = m := by
    have hc := halfRows_card μ he
    omega
  let s := canonicalTableau (halfRows μ) hm
  let es : Fin n ≃ Fin m ⊕ Fin m := t.trans ((pairedCells μ he).symm.trans
    (Equiv.sumCongr s.symm s.symm))
  have ht : pairedTableau μ he es s = t := by
    apply Equiv.ext
    intro i
    change pairedCells μ he ((Equiv.sumCongr s s)
      ((Equiv.sumCongr s s).symm ((pairedCells μ he).symm (t i)))) = t i
    simp only [Equiv.apply_symm_apply]
  let φ : Fin (μ.colLen 0) → Fin d := Fin.castLE hd
  have hh : dotProduct (letterLift φ (polytabloid t)) (symmetricPairs es d) ≠ 0 := by
    rw [letterLift_symmetricPairs_pair _ φ (Fin.castLE_injective hd), ← ht]
    exact pairedTableau_contraction μ he es s
  have hsupp := hom_to_cyclic_of_pair
    (fun a b => if φ a = b then 1 else 0) (spechtSub t)
    ⟨polytabloid t, mem_cyclic _ _⟩ (symmetricPairs es d) (symmetricPairs_real es) hh
  let g : Equiv.Perm (Fin n) := e.trans es.symm
  have hg : wordRep n d g (symmetricPairs e d) = symmetricPairs es d := by
    funext w
    have hl : leftWord e (w ∘ g) = leftWord es w := by
      funext i
      simp [leftWord, g]
    have hr : rightWord e (w ∘ g) = rightWord es w := by
      funext i
      simp [rightWord, g]
    change (if leftWord e (w ∘ g) = rightWord e (w ∘ g) then 1 else 0) = _
    simp only [hl, hr, symmetricPairs]
  have hc : cyclic (wordRep n d) (symmetricPairs es d) =
      cyclic (wordRep n d) (symmetricPairs e d) := by
    rw [← hg, cyclic_action_eq]
  change ∃ f : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (symmetricPairs es d)).toRepresentation, f ≠ 0 at hsupp
  rw [hc] at hsupp
  exact hsupp

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_PairForms
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Forms. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma pairFormTensor_one {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) :
    pairFormTensor e (1 : Matrix (Fin d) (Fin d) ℂ) = symmetricPairs e d := by
  classical
  funext w
  change (∏ i, if leftWord e w i = rightWord e w i then (1 : ℂ) else 0) = _
  by_cases hw : leftWord e w = rightWord e w
  · simp [hw, symmetricPairs]
  · have hi : ∃ i, leftWord e w i ≠ rightWord e w i := by
      exact not_forall.mp (fun he => hw (funext he))
    obtain ⟨i, hi⟩ := hi
    rw [symmetricPairs, ite_eq_right hw]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma wordMap_pairFormTensor {n m a b : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (L : Fin a → Fin b → ℂ) (B : Matrix (Fin a) (Fin a) ℂ) :
    wordMap L (pairFormTensor e B) = pairFormTensor e
      (fun j k => ∑ p : Fin a × Fin a, B p.1 p.2 * L p.1 j * L p.2 k) := by
  classical
  funext w
  change (∑ c, pairFormTensor e B c * ∏ i, L (c i) (w i)) = _
  calc
    _ = ∑ c : Fin m → Fin a × Fin a,
        ∏ i, B (c i).1 (c i).2 * L (c i).1 (leftWord e w i) *
          L (c i).2 (rightWord e w i) := by
      apply Fintype.sum_equiv (pairWordsEquiv e)
      intro c
      simp only [pairWordsEquiv_apply, pairFormTensor, Finset.prod_mul_distrib]
      have he : (∏ i, L (c i) (w i)) =
          (∏ i, L (leftWord e c i) (leftWord e w i)) *
            ∏ i, L (rightWord e c i) (rightWord e w i) := by
        calc
          _ = ∏ x : Fin m ⊕ Fin m, L (c (e.symm x)) (w (e.symm x)) :=
            (Equiv.prod_comp e.symm (fun i => L (c i) (w i))).symm
          _ = _ := by
            rw [Fintype.prod_sum_type]
            rfl
      rw [he, mul_assoc]
    _ = _ := by
      change (∑ c : Fin m → Fin a × Fin a,
        ∏ i, B (c i).1 (c i).2 * L (c i).1 (leftWord e w i) *
          L (c i).2 (rightWord e w i)) =
        ∏ i, ∑ p : Fin a × Fin a,
          B p.1 p.2 * L p.1 (leftWord e w i) * L p.2 (rightWord e w i)
      exact (Fintype.prod_sum (fun (i : Fin m) (p : Fin a × Fin a) =>
        B p.1 p.2 * L p.1 (leftWord e w i) * L p.2 (rightWord e w i))).symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_RepeatedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem specht_map_back_of_nonzero {n : ℕ} {μ : YoungDiagram}
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X) (t : Tableau n μ)
    (F : Representation.IntertwiningMap ρ (spechtRep t)) (hF : F ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRep t) ρ, f ≠ 0 := by
  let := specht_irreducible t
  have hs : Function.Surjective F :=
    (Representation.IsIrreducible.surjective_or_eq_zero F).resolve_right hF
  obtain ⟨f, hf⟩ := intertwining_lift_surjective F hs
    (Representation.IntertwiningMap.id (spechtRep t))
  refine ⟨f, ?_⟩
  intro hz
  have he := congrArg (fun H : Representation.IntertwiningMap (spechtRep t) (spechtRep t) =>
    H ⟨polytabloid t, mem_cyclic _ _⟩) hf
  change F (f _) = _ at he
  rw [hz] at he
  change F 0 = _ at he
  rw [map_zero] at he
  exact polytabloid_ne_zero t (congrArg Subtype.val he.symm)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_GeneralDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! General Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma wordMap_pair_transpose {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (x : WordSpace n d) (y : WordSpace n e) :
    dotProduct (wordMap L x) y = dotProduct x (wordMap (fun b a => L a b) y) := by
  classical
  change (∑ b, (∑ a, x a * ∏ i, L (a i) (b i)) * y b) =
    ∑ a, x a * ∑ b, y b * ∏ i, L (a i) (b i)
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SingletonPairs
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton Pairs. -/

section

noncomputable section
namespace Saxl

lemma wordMap_positionProduct {n a b d D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (L : Fin d → Fin D → ℂ) (x : WordSpace a d) (y : WordSpace b d) :
    wordMap L (positionProduct e x y) =
      positionProduct e (wordMap L x) (wordMap L y) := by
  classical
  funext w
  change (∑ c, (x (leftWord e c) * y (rightWord e c)) * ∏ i, L (c i) (w i)) = _
  calc
    _ = ∑ p : (Fin a → Fin d) × (Fin b → Fin d),
        (x p.1 * ∏ i, L (p.1 i) (leftWord e w i)) *
          (y p.2 * ∏ i, L (p.2 i) (rightWord e w i)) := by
      apply Fintype.sum_equiv (positionWordsEquiv e)
      intro c
      have he : (∏ i, L (c i) (w i)) =
          (∏ i, L (leftWord e c i) (leftWord e w i)) *
            ∏ i, L (rightWord e c i) (rightWord e w i) := by
        calc
          _ = ∏ z : Fin a ⊕ Fin b, L (c (e.symm z)) (w (e.symm z)) :=
            (Equiv.prod_comp e.symm (fun i => L (c i) (w i))).symm
          _ = _ := by rw [Fintype.prod_sum_type]; rfl
      rw [he]
      change _ = (x (leftWord e c) * _) * (y (rightWord e c) * _)
      dsimp [positionWordsEquiv]
      ring
    _ = _ := by
      change _ = (∑ c, x c * ∏ i, L (c i) (leftWord e w i)) *
        (∑ c, y c * ∏ i, L (c i) (rightWord e w i))
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      simp only [Finset.mul_sum]

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_PolynomialDetection
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma jointContent_apply {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e)
    (j : Fin d × Fin e) : jointContent a b j =
      (Finset.univ.filter (fun i => (a i, b i) = j)).card := by
  classical
  simp [jointContent, Finsupp.single_apply, eq_comm]

lemma perm_of_equal_jointContent {n d e : ℕ}
    (a a' : Fin n → Fin d) (b b' : Fin n → Fin e)
    (h : jointContent a b = jointContent a' b') :
    ∃ g : Equiv.Perm (Fin n), a' ∘ g = a ∧ b' ∘ g = b := by
  classical
  have hc : ∀ j : Fin (d*e),
      (Finset.univ.filter (fun i => finProdFinEquiv (a i,b i) = j)).card =
      (Finset.univ.filter (fun i => finProdFinEquiv (a' i,b' i) = j)).card := by
    intro j
    have hh := DFunLike.congr_fun h (finProdFinEquiv.symm j)
    simp only [jointContent_apply] at hh
    simpa only [← Equiv.eq_symm_apply] using hh
  obtain ⟨g, hg⟩ := perm_of_equal_content
    (fun i => finProdFinEquiv (a i, b i))
    (fun i => finProdFinEquiv (a' i, b' i)) hc
  refine ⟨g, ?_, ?_⟩
  · funext i
    exact congrArg Prod.fst (finProdFinEquiv.injective (congrFun hg i))
  · funext i
    exact congrArg Prod.snd (finProdFinEquiv.injective (congrFun hg i))

lemma intertwiner_jointContent {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (a a' : Fin n → Fin d) (b b' : Fin n → Fin e)
    (h : jointContent a b = jointContent a' b') :
    F (Pi.single a 1) b = F (Pi.single a' 1) b' := by
  classical
  obtain ⟨g, ha, hb⟩ := perm_of_equal_jointContent a a' b b' h
  have hs : wordRep n d g (Pi.single a 1) = Pi.single a' 1 := by
    ext w
    change (Pi.single a 1 : WordSpace n d) (w ∘ g) = (Pi.single a' 1 : WordSpace n d) w
    simp only [Pi.single_apply]
    have he : (w ∘ g = a) ↔ w = a' := by
      rw [← ha]
      exact ⟨fun h => funext (fun i => by
        have hh := congrFun h (g⁻¹ i)
        simpa using hh),
        fun h => by rw [h]⟩
    simp only [he]
  have hh := congrFun (LinearMap.congr_fun (F.isIntertwining' g) (Pi.single a 1)) b'
  simp only [LinearMap.comp_apply] at hh
  rw [hs] at hh
  change F (Pi.single a' 1) b' = F (Pi.single a 1) (b' ∘ g) at hh
  rw [hb] at hh
  exact hh.symm

lemma eval_jointContent_monomial {n d e : ℕ}
    (a : Fin n → Fin d) (b : Fin n → Fin e)
    (c : ℂ) (L : Fin d → Fin e → ℂ) :
    MvPolynomial.eval (fun j => L j.1 j.2)
      (MvPolynomial.monomial (jointContent a b) c) =
      c * ∏ i, L (a i) (b i) := by
  classical
  rw [jointContent, MvPolynomial.monomial_sum_index]
  simp only [map_mul, MvPolynomial.eval_C, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  change MvPolynomial.eval _ (MvPolynomial.X (a i, b i)) = _
  exact MvPolynomial.eval_X _

lemma pairingPolynomial_eval {n d e : ℕ}
    (x : WordSpace n d) (y : WordSpace n e) (L : Fin d → Fin e → ℂ) :
    MvPolynomial.eval (fun j => L j.1 j.2) (pairingPolynomial x y) =
      dotProduct (wordMap L x) y := by
  classical
  simp only [pairingPolynomial, map_sum, eval_jointContent_monomial]
  change (∑ a, ∑ b, x a * y b * ∏ i, L (a i) (b i)) =
    ∑ b, (∑ a, x a * ∏ i, L (a i) (b i)) * y b
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma jointContentWeight_apply {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (a : Fin n → Fin d) (b : Fin n → Fin e) :
    jointContentWeight F (jointContent a b) = F (Pi.single a 1) b := by
  classical
  unfold jointContentWeight
  have hab : ∃ a' b', jointContent a' b' = jointContent a b := ⟨a,b,rfl⟩
  rw [dite_eq_left hab]
  exact intertwiner_jointContent F _ a _ b hab.choose_spec.choose_spec

lemma pairingPolynomial_zero_pair {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (x : WordSpace n d) (y : WordSpace n e) (h : pairingPolynomial x y = 0) :
    dotProduct (F x) y = 0 := by
  classical
  let w : MvPolynomial (Fin d × Fin e) ℂ →ₗ[ℂ] ℂ :=
    (Finsupp.linearCombination ℂ (jointContentWeight F)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
  have he := congrArg w h
  have hw (m : (Fin d × Fin e) →₀ ℕ) (c : ℂ) :
      w (MvPolynomial.monomial m c) = c * jointContentWeight F m := by
    change Finsupp.linearCombination ℂ (jointContentWeight F) (Finsupp.single m c) = _
    simp
  have he' : (∑ a, ∑ b, (x a * y b) * F (Pi.single a 1) b) = 0 := by
    simpa only [pairingPolynomial, map_sum, map_zero, hw, jointContentWeight_apply] using he
  have hx : x = ∑ a, x a • Pi.single a 1 := by
    ext a
    simp [Pi.single_apply]
  rw [hx, map_sum]
  simp only [map_smul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  convert he' using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem wordMap_detects_intertwiner {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (x : WordSpace n d) (y : WordSpace n e)
    (h : dotProduct (F x) y ≠ 0) :
    ∃ L : Fin d → Fin e → ℂ, dotProduct (wordMap L x) y ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  apply pairingPolynomial_zero_pair F
  apply MvPolynomial.funext
  intro L
  simpa only [map_zero, pairingPolynomial_eval] using
    (pairingPolynomial_eval x y (fun a b => L (a,b))).trans (hn _)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_DualPolytabloid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual Polytabloid. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl
open scoped MonoidAlgebra

theorem dual_polytabloid_necessary {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (u : WordSpace n d)
    (f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation) (hf : f ≠ 0) :
    ∃ (g : Equiv.Perm (Fin n)) (L : Fin (μ.colLen 0) → Fin d → ℂ),
      dotProduct (wordMap L (wordRep n (μ.colLen 0) g (polytabloid t))) u ≠ 0 := by
  let := specht_irreducible t
  have hfi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let E := (subrepInclusion (cyclic (wordRep n d) u)).comp f
  have hEi : Function.Injective E := Subtype.val_injective.comp hfi
  obtain ⟨R, hR⟩ := intertwining_extend_injective E hEi
    (Representation.IntertwiningMap.id (spechtRep t))
  have hRu : R u ≠ 0 := by
    intro h0
    let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
    have hm := intertwiner_cyclic_mem R u (E p) (f p).property
    rw [h0, cyclic_zero_mem_iff] at hm
    have hi := congrArg (fun H : Representation.IntertwiningMap (spechtRep t)
      (spechtRep t) => H p) hR
    change R (E p) = p at hi
    exact polytabloid_ne_zero t (congrArg Subtype.val (hi.symm.trans hm))
  have hv : (R u).val ≠ 0 := by
    intro hz
    exact hRu (Subtype.ext hz)
  obtain ⟨g, hg⟩ := specht_detect t (R u).property hv
  let F := (subrepInclusion (spechtSub t)).comp R
  have hp : dotProduct (F u)
      (wordRep n (μ.colLen 0) g⁻¹ (polytabloid t)) ≠ 0 := by
    rw [wordPair_move] at hg
    exact hg
  obtain ⟨L,hL⟩ := wordMap_detects_intertwiner F u _ hp
  refine ⟨g⁻¹, fun b a => L a b, ?_⟩
  rw [wordMap_pair_transpose, dotProduct_comm] at hL
  exact hL

theorem specht_to_cyclic_of_vector_pair {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (x : Specht t) (L : Fin (μ.colLen 0) → Fin d → ℂ)
    (u : WordSpace n d)
    (h : dotProduct (wordMap L x.val) u ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, F ≠ 0 := by
  let pr := subrepProject (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
  let F : Representation.IntertwiningMap
      (cyclic (wordRep n d) u).toRepresentation (spechtRep t) :=
    pr.comp ((wordMap (fun b a => L a b)).comp (subrepInclusion _))
  apply specht_map_back_of_nonzero _ t F
  intro hz
  have hp := subrepProject_pair (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
    (wordMap (fun b a => L a b) u) x
  have he : pr (wordMap (fun b a => L a b) u) = 0 :=
    congrArg (fun H : Representation.IntertwiningMap
      (cyclic (wordRep n d) u).toRepresentation (spechtRep t) =>
      H ⟨u, mem_cyclic _ _⟩) hz
  rw [he] at hp
  change dotProduct (0 : WordSpace n (μ.colLen 0)) x.val =
    dotProduct (wordMap (fun b a => L a b) u) x.val at hp
  rw [zero_dotProduct] at hp
  rw [wordMap_pair_transpose, dotProduct_comm] at h
  exact h hp.symm

theorem dual_polytabloid_iff {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (u : WordSpace n d) :
    (∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, f ≠ 0) ↔
    ∃ (g : Equiv.Perm (Fin n)) (L : Fin (μ.colLen 0) → Fin d → ℂ),
      dotProduct (wordMap L (wordRep n (μ.colLen 0) g (polytabloid t))) u ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact dual_polytabloid_necessary t u f hf
  · rintro ⟨g, L, h⟩
    exact specht_to_cyclic_of_vector_pair t
      ⟨wordRep n (μ.colLen 0) g (polytabloid t),
        (spechtSub t).apply_mem_toSubmodule g (mem_cyclic _ _)⟩ L u h

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CommonBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common Basis. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma wordMap_letterLift {n a b c : ℕ} (f : Fin a → Fin b)
    (L : Fin b → Fin c → ℂ) (x : WordSpace n a) :
    wordMap L (letterLift f x) = wordMap (fun i j => L (f i) j) x := by
  classical
  have h : (wordMap L).comp (letterLift f) = wordMap (fun i j => L (f i) j) (n := n) := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.pi_ext
    intro w c
    have he : (Pi.single w c : WordSpace n a) = c • Pi.single w 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [he, map_smul, map_smul]
    congr 1
    change wordMap L (letterLift f (Pi.single w 1)) = wordMap _ (Pi.single w 1)
    rw [letterLift_single]
    ext v
    simp only [wordMap_single, Function.comp_apply]
  exact congrArg (fun F => F x) h

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_BandContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Contractions. -/

section

noncomputable section
namespace Saxl

lemma positionProduct_alphabet {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (P : Fin d → Prop) (v : WordSpace a d) (u : WordSpace b d)
    (hv : v ∈ alphabetSub a d P) (hu : u ∈ alphabetSub b d P) :
    positionProduct e v u ∈ alphabetSub n d P := by
  intro w hw
  obtain ⟨i,hi⟩ := hw
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j =>
    change v (leftWord e w) * u (rightWord e w) = 0
    rw [hv _ ⟨j,hi⟩, zero_mul]
  | inr j =>
    change v (leftWord e w) * u (rightWord e w) = 0
    rw [hu _ ⟨j,hi⟩, mul_zero]

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Density. -/

section

noncomputable section
open scoped Topology

namespace Saxl.ThreeRow

lemma gram_hasStrictFDerivAt (z : Parameters) (i j : Fin 3) :
    HasStrictFDerivAt (fun z => gram z i j) (gramDeriv z i j) z := by
  have h (k : Fin 13) := hasStrictFDerivAt_apply (𝕜 := ℂ) k z
  exact ((h 12).mul (((h (idx 2 i)).mul (h (idx 3 j))).add
    ((h (idx 2 j)).mul (h (idx 3 i))))).sub
      (((h (idx 0 i)).mul (h (idx 1 j))).add ((h (idx 0 j)).mul (h (idx 1 i))))

lemma parameterMap_hasStrictFDerivAt (z : Parameters) :
    HasStrictFDerivAt parameterMap (parameterDeriv z) z := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  fin_cases i
  all_goals first
    | exact gram_hasStrictFDerivAt z 0 0
    | exact gram_hasStrictFDerivAt z 0 1
    | exact gram_hasStrictFDerivAt z 0 2
    | exact gram_hasStrictFDerivAt z 1 1
    | exact gram_hasStrictFDerivAt z 1 2
    | exact gram_hasStrictFDerivAt z 2 2
    | exact hasStrictFDerivAt_apply (𝕜 := ℂ) _ z

lemma differential_lift (w : Coordinates) :
    parameterDeriv basePoint (differentialLift w) = w := by
  funext i
  fin_cases i <;>
    simp [parameterDeriv, gramDeriv, basePoint, differentialLift,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, proj, idx, Matrix.cons_val,
      Fin.reduceFinMk] <;>
    ring

lemma parameterDeriv_surjective : Function.Surjective (parameterDeriv basePoint) :=
  fun w => ⟨differentialLift w, differential_lift w⟩

theorem joint_density (F : Coordinates → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ)
    (hzero : ∀ z : Parameters, z 12 ≠ 0 → F (parameterMap z) = 0) :
    ∀ w, F w = 0 := by
  have hopen := (parameterMap_hasStrictFDerivAt basePoint).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr parameterDeriv_surjective)
  have ht : ∀ᶠ z : Parameters in 𝓝 basePoint, z 12 ≠ 0 := by
    apply (isOpen_ne_fun (continuous_apply 12) continuous_const).mem_nhds
    change (1 : ℂ) ≠ 0
    exact one_ne_zero
  have hz : ∀ᶠ w in 𝓝 (parameterMap basePoint), F w = 0 := by
    rw [← hopen, Filter.eventually_map]
    exact ht.mono hzero
  have heq := hF.eq_of_eventuallyEq
    (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : Coordinates => (0 : ℂ)) Set.univ) hz
  intro w
  exact congrFun heq w

end Saxl.ThreeRow
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowPieri
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Pieri. -/

section

noncomputable section
namespace Saxl

lemma constant_word_support {n d : ℕ} (a : Fin d) (μ : YoungDiagram)
    (t : Tableau n μ) (hμ : μ.colLen 0 ≤ 1) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (Pi.single (fun _ => a) 1)).toRepresentation, F ≠ 0 := by
  classical
  let φ : Fin (μ.colLen 0) → Fin d := fun _ => a
  have hφ : Function.Injective φ := by
    intro i j hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  let G := (letterLift φ).comp (spechtInclusion t)
  have hG (x : Specht t) : G x ∈ cyclic (wordRep n d) (Pi.single (fun _ => a) 1) := by
    change letterLift φ x.val ∈ _
    rw [← (Pi.basisFun ℂ (Fin n → Fin (μ.colLen 0))).sum_repr x.val]
    simp only [map_sum,map_smul,Pi.basisFun_apply,letterLift_single]
    apply Submodule.sum_mem
    intro w hw
    exact Submodule.smul_mem _ _ (mem_cyclic _ _)
  let F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (Pi.single (fun _ => a) 1)).toRepresentation := {
    toLinearMap := G.toLinearMap.codRestrict _ hG
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (G.isIntertwining' g) x }
  refine ⟨F,?_⟩
  intro hz
  have he := congrArg (fun Q : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (Pi.single (fun _ => a) 1)).toRepresentation =>
      (Q ⟨polytabloid t,mem_cyclic _ _⟩).val) hz
  change letterLift φ (polytabloid t) = 0 at he
  exact polytabloid_ne_zero t ((letterLift_injective φ hφ) (he.trans (map_zero _).symm))

lemma lift_cyclic_support {n a d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (φ : Fin a → Fin d) (hφ : Function.Injective φ) (v : WordSpace n a)
    (hs : ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n a) v).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (letterLift φ v)).toRepresentation, F ≠ 0 := by
  obtain ⟨F,hF⟩ := hs
  refine ⟨(cyclicMap (letterLift φ) v).comp F,?_⟩
  intro hz
  apply hF
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply letterLift_injective φ hφ
  have he := congrArg (fun Q : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (letterLift φ v)).toRepresentation => (Q x).val) hz
  change letterLift φ (F x).val = 0 at he
  change letterLift φ (F x).val = letterLift φ 0
  simpa only [map_zero] using he

namespace ThreeRow

theorem colorTensor_support {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    {ν η μ : YoungDiagram} (tν : Tableau a ν) (tη : Tableau r η) (tμ : Tableau n μ)
    (hev : ∀ i, Even (ν.rowLen i)) (hν : ν.colLen 0 ≤ 3)
    (hs : HorizontalStrip ν η) (ht : HorizontalStrip η μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep tμ)
      (cyclic (wordRep n 5) (colorTensor q p e)).toRepresentation, F ≠ 0 := by
  have hv : letterLift (Fin.castAdd 2) (symmetricPairs q 3) ∈
      alphabetSub a 5 (fun z => z.val < 3) := by
    apply letterLift_mem_alphabet
    intro i
    exact i.isLt
  have hu : (Pi.single (fun _ : Fin s => (3 : Fin 5)) (1 : ℂ)) ∈
      alphabetSub s 5 (fun z => ¬ z.val < 3) :=
    single_mem_alphabet _ _ (by intro i; decide)
  obtain ⟨F,hF⟩ := lift_cyclic_support tν (Fin.castAdd 2) (Fin.castAdd_injective 3 2) _
    (even_rows_symmetricPairs_support q ν tν hev hν)
  obtain ⟨G,hG⟩ := strip_product_support (SizedStripChain.of_horizontal hs) tν tη p _ _
    (fun z => z.val < 3) hv hu F hF (by
      intro ξ tξ hξ
      exact constant_word_support 3 ξ tξ hξ)
  refine strip_product_support (SizedStripChain.of_horizontal ht) tη tμ e
    (positionProduct p (letterLift (Fin.castAdd 2) (symmetricPairs q 3))
      (Pi.single (fun _ => (3 : Fin 5)) 1))
    (Pi.single (fun _ => (4 : Fin 5)) 1) (fun z => z.val < 4) ?_ ?_ G hG ?_
  · refine positionProduct_alphabet p (fun z => z.val < 4) _ _ ?_ ?_
    · apply letterLift_mem_alphabet
      intro i
      change i.val < 4
      have := i.isLt
      omega
    · exact single_mem_alphabet _ _ (by intro i; decide)
  · exact single_mem_alphabet _ _ (by intro i; decide)
  · intro ξ tξ hξ
    exact constant_word_support 4 ξ tξ hξ

end ThreeRow
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowTensors
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Tensors. -/

section

noncomputable section
namespace Saxl.ThreeRow

lemma wordMap_constant {n a d : ℕ} (L : Fin a → Fin d → ℂ) (k : Fin a) :
    wordMap L (Pi.single (fun _ : Fin n => k) 1) = powerVector n (L k) := by
  ext w
  exact wordMap_single L (fun _ => k) w

lemma gram_symm (z : Parameters) (i j : Fin 3) : gram z i j = gram z j i := by
  unfold gram
  ring

lemma matrixCoord_parameter (z : Parameters) : matrixCoord (parameterMap z) = gram z := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixCoord,parameterMap,symmetricIndex,Matrix.cons_val,gram_symm] <;>
      exact gram_symm _ _ _

lemma xCoord_parameter (z : Parameters) : xCoord (parameterMap z) = fun i => z (idx 2 i) := by
  funext i
  fin_cases i <;> rfl

lemma yCoord_parameter (z : Parameters) : yCoord (parameterMap z) = fun i => z (idx 3 i) := by
  funext i
  fin_cases i <;> rfl

lemma independentFamily_analytic {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    (v : WordSpace n 3) :
    AnalyticOnNhd ℂ (fun w => dotProduct v (independentFamily q p e w)) Set.univ := by
  intro w hw
  unfold dotProduct independentFamily independentTensor positionProduct pairFormTensor powerVector
  apply Finset.analyticAt_fun_sum
  intro c hc
  apply AnalyticAt.mul analyticAt_const
  apply AnalyticAt.mul
  · apply AnalyticAt.mul
    · apply Finset.analyticAt_fun_prod
      intro i hi
      exact (ContinuousLinearMap.proj _ : Coordinates →L[ℂ] ℂ).analyticAt w
    · apply Finset.analyticAt_fun_prod
      intro i hi
      exact (ContinuousLinearMap.proj _ : Coordinates →L[ℂ] ℂ).analyticAt w
  · apply Finset.analyticAt_fun_prod
    intro i hi
    exact (ContinuousLinearMap.proj _ : Coordinates →L[ℂ] ℂ).analyticAt w

lemma matrixCoord_pack (Q : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ)
    (h : ∀ i j, Q i j = Q j i) : matrixCoord (packCoordinates Q x y) = Q := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixCoord,packCoordinates,symmetricIndex,Matrix.cons_val,h] <;> exact h _ _

lemma xCoord_pack (Q : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) :
    xCoord (packCoordinates Q x y) = x := by
  funext i
  fin_cases i <;> rfl

lemma yCoord_pack (Q : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) :
    yCoord (packCoordinates Q x y) = y := by
  funext i
  fin_cases i <;> rfl

lemma independentFamily_pack {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    (Q : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) (h : ∀ i j, Q i j = Q j i) :
    independentFamily q p e (packCoordinates Q x y) = independentTensor q p e Q x y := by
  rw [independentFamily,matrixCoord_pack Q x y h,xCoord_pack,yCoord_pack]

lemma wordMap_symmetricPairs {n m d : ℕ} (q : Fin n ≃ Fin m ⊕ Fin m)
    (L : Fin d → Fin 3 → ℂ) :
    wordMap L (symmetricPairs q d) = pairFormTensor q (fun i j => ∑ k, L k i * L k j) := by
  rw [← pairFormTensor_one,wordMap_pairFormTensor]
  congr 1
  funext i j
  simp [Fintype.sum_prod_type,Matrix.one_apply]

lemma colorTensor_image {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    (L : Fin 5 → Fin 3 → ℂ) :
    wordMap L (colorTensor q p e) = independentTensor q p e
      (fun i j => ∑ k : Fin 3, L (Fin.castAdd 2 k) i * L (Fin.castAdd 2 k) j)
      (L 3) (L 4) := by
  rw [colorTensor,wordMap_positionProduct,wordMap_positionProduct,wordMap_letterLift,
    wordMap_symmetricPairs,wordMap_constant,wordMap_constant]
  rfl

theorem independent_nonvanishing {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    {μ : YoungDiagram} (t : Tableau n μ) (ht : μ.colLen 0 ≤ 3)
    (hs : ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 5) (colorTensor q p e)).toRepresentation, F ≠ 0) :
    ∃ (g : Equiv.Perm (Fin n)) (w : Coordinates),
      dotProduct (letterLift (Fin.castLE ht) (wordRep n (μ.colLen 0) g (polytabloid t)))
        (independentFamily q p e w) ≠ 0 := by
  classical
  obtain ⟨F,hF⟩ := hs
  obtain ⟨g,L,hL⟩ := dual_polytabloid_necessary t _ F hF
  let B : Fin 3 → Fin 5 → ℂ := fun i j => if hi : i.val < μ.colLen 0 then L ⟨i.val,hi⟩ j else 0
  have hB (i : Fin (μ.colLen 0)) (j : Fin 5) : B (Fin.castLE ht i) j = L i j := by
    simp [B,i.isLt]
  have hpair : dotProduct
      (letterLift (Fin.castLE ht) (wordRep n (μ.colLen 0) g (polytabloid t)))
      (wordMap (fun j i => B i j) (colorTensor q p e)) ≠ 0 := by
    rw [← wordMap_pair_transpose,wordMap_letterLift]
    simpa only [hB] using hL
  rw [colorTensor_image] at hpair
  let Q : Matrix (Fin 3) (Fin 3) ℂ := fun i j => ∑ k : Fin 3,
    B i (Fin.castAdd 2 k) * B j (Fin.castAdd 2 k)
  have hQ (i j : Fin 3) : Q i j = Q j i := by
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  refine ⟨g, packCoordinates Q (fun i => B i 3) (fun i => B i 4), ?_⟩
  rwa [independentFamily_pack q p e Q _ _ hQ]

end Saxl.ThreeRow
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowGenerator
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Generator. -/

section

noncomputable section
namespace Saxl.ThreeRow

lemma densityMap_triple (z : Parameters) (i : Fin 3) :
    densityMap z (tripleColors i) = fun j => z 12 * z (idx 3 j) := by
  fin_cases i <;> rfl

lemma densityMap_form (z : Parameters) :
    (fun i j => ∑ k : Fin 6 × Fin 6,
      sixPairForm k.1 k.2 * densityMap z k.1 i * densityMap z k.2 j) = gram z := by
  funext i j
  simp [Fintype.sum_prod_type,Fin.sum_univ_succ,sixPairForm,densityMap,gram]
  ring

lemma densityMap_symmetricTriple (z : Parameters) :
    wordMap (densityMap z) symmetricTriple =
      (6 * z 12^3) • powerVector 3 (fun i => z (idx 3 i)) := by
  classical
  have h (g : Equiv.Perm (Fin 3)) :
      wordMap (densityMap z) (Pi.single (tripleColors ∘ g) 1) =
        z 12^3 • powerVector 3 (fun i => z (idx 3 i)) := by
    funext w
    simp only [wordMap_single, Function.comp_apply, densityMap_triple]
    simp [powerVector, Finset.prod_mul_distrib]
  rw [symmetricTriple,map_sum]
  simp only [h,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin]
  norm_num [← Nat.cast_smul_eq_nsmul ℂ,smul_smul]

lemma generator_image {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3) (z : Parameters) :
    wordMap (densityMap z) (generator q p e) =
      (6 * z 12^3) • independentFamily q p e (parameterMap z) := by
  rw [generator,wordMap_positionProduct,wordMap_positionProduct,wordMap_pairFormTensor,
    densityMap_form,wordMap_constant,densityMap_symmetricTriple,independentFamily,
    matrixCoord_parameter,xCoord_parameter,yCoord_parameter]
  funext w
  change _ * ((6*z 12^3) * _) = (6*z 12^3) * (_ * _)
  change (pairFormTensor q (gram z) (leftWord p (leftWord e w)) *
    powerVector s (fun i => z (idx 2 i)) (rightWord p (leftWord e w))) *
    ((6*z 12^3) * powerVector 3 (fun i => z (idx 3 i)) (rightWord e w)) = _
  dsimp [positionProduct]
  ring

theorem generator_support_of_colorTensor {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    {μ : YoungDiagram} (t : Tableau n μ) (ht : μ.colLen 0 ≤ 3)
    (hs : ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 5) (colorTensor q p e)).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 6) (generator q p e)).toRepresentation, F ≠ 0 := by
  obtain ⟨g,w,hw⟩ := independent_nonvanishing q p e t ht hs
  let x := letterLift (Fin.castLE ht) (wordRep n (μ.colLen 0) g (polytabloid t))
  have hex : ∃ z : Parameters, z 12 ≠ 0 ∧
      dotProduct x (independentFamily q p e (parameterMap z)) ≠ 0 := by
    by_contra! hn
    exact hw (joint_density _ (independentFamily_analytic q p e x) hn w)
  obtain ⟨z,hz,hpair⟩ := hex
  have hnonzero : dotProduct x (wordMap (densityMap z) (generator q p e)) ≠ 0 := by
    rw [generator_image,dotProduct_smul]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hz)) hpair
  rw [← wordMap_pair_transpose] at hnonzero
  change dotProduct (wordMap _ (letterLift (Fin.castLE ht)
    (wordRep n (μ.colLen 0) g (polytabloid t)))) (generator q p e) ≠ 0 at hnonzero
  rw [wordMap_letterLift] at hnonzero
  exact (dual_polytabloid_iff t _).mpr ⟨g,_,hnonzero⟩

theorem generator_support_oai {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    {ν η μ : YoungDiagram} (tν : Tableau a ν) (tη : Tableau r η) (tμ : Tableau n μ)
    (hev : ∀ i, Even (ν.rowLen i)) (hν : ν.colLen 0 ≤ 3) (hμ : μ.colLen 0 ≤ 3)
    (hs : HorizontalStrip ν η) (ht : HorizontalStrip η μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep tμ)
      (cyclic (wordRep n 6) (generator q p e)).toRepresentation, F ≠ 0 :=
  generator_support_of_colorTensor q p e tμ hμ
    (colorTensor_support q p e tν tη tμ hev hν hs ht)

end Saxl.ThreeRow
end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.ThreeRow.generator_support_oai := @OAI.Saxl.ThreeRow.generator_support_oai
