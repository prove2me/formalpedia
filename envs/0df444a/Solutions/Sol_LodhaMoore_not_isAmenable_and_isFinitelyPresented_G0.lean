-- Prove2me | solution 1 for LodhaMoore.not_isAmenable_and_isFinitelyPresented_G0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.834962+00:00
-- url     : https://prove2.me/submissions/a5e8fa03-b66a-4344-a6d0-5d94b94c4f8d

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_LodhaMooreWords
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Monod_PiecewiseProjective
import Theorems.Thm_LodhaMoore_isMuAmenable_orbit_of_isAmenable
import Theorems.Thm_LodhaMoore_range_SL2Z_lt_K_and_dense_and_not_isMuAmenable
import Theorems.Thm_LodhaMoore_orbit_G0_eq_orbit_K_of_irrational
import Theorems.Thm_LodhaMoore_exists_mulEquiv_G0_G0Seq_and_semiconj_Phi
import Theorems.Thm_LodhaMoore_presentation_G_G0Seq_and_isFinitelyPresented

section
/-!
# Lodha–Moore: Theorem 3.3 and Theorem 1.1

Theorem 3.3 (`R` presents `G`, `R₀` presents `G₀`, both finitely presented) by the argument at the
end of §5, and Theorem 1.1 (the goal).
-/

namespace LodhaMoore.Dev.Top

open LodhaMoore

/-! ### Constant sequences -/


/-! ### Words evaluated in an arbitrary group -/

section EvalW

variable {H : Type*} [Group H]

/-- The value of a word when the generator `g` is sent to `f g`, multiplied left to right. -/
def evalW (f : Gen → H) (Ω : Word) : H := (Ω.map fun p => f p.1 ^ p.2).prod

@[simp] lemma evalW_nil (f : Gen → H) : evalW f [] = 1 := rfl

@[simp] lemma evalW_cons (f : Gen → H) (p : Gen × ℤ) (Ω : Word) :
    evalW f (p :: Ω) = f p.1 ^ p.2 * evalW f Ω := by
  simp [evalW]

@[simp] lemma evalW_append (f : Gen → H) (A B : Word) :
    evalW f (A ++ B) = evalW f A * evalW f B := by
  simp [evalW]

end EvalW

/-! ### From a derivation to the presentation (end of §5) -/

section Inj

variable {H : Type*} [Group H]

end Inj

/-! ### Theorem 1.1: nonamenability (§2) -/

section Amen

open MeasureTheory

theorem polishSpace_P1 : PolishSpace (OnePoint ℝ) := by
  have e := onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)
  have : PolishSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    Metric.isClosed_sphere.polishSpace
  exact e.isClosedEmbedding.polishSpace

theorem sigmaFinite_volP1 : SigmaFinite Monod.volP1 :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding.sigmaFinite_map

lemma volP1_countable {Z : Set (OnePoint ℝ)} (hZ : Z.Countable) : Monod.volP1 Z = 0 := by
  rw [Monod.volP1, OnePoint.isOpenEmbedding_coe.measurableEmbedding.map_apply]
  exact (hZ.preimage OnePoint.coe_injective).measure_zero _

/-- A `μ`-amenable relation stays `μ`-amenable when it is changed only on a null set whose
complement is invariant. -/
lemma isMuAmenable_transfer {X : Type*} [MeasurableSpace X] {μ : Measure X} {E E' : Set (X × X)}
    (hE : IsMuAmenable μ E) (Z : Set X) (hZm : MeasurableSet Z) (hZ0 : μ Z = 0)
    (hinv : ∀ x y, (x, y) ∈ E → x ∉ Z → y ∉ Z)
    (hagree : ∀ x y, x ∉ Z → y ∉ Z → ((x, y) ∈ E ↔ (x, y) ∈ E')) : IsMuAmenable μ E' := by
  obtain ⟨N, hNm, hN0, T, hT⟩ := hE
  refine ⟨N ∪ Z, hNm.union hZm, measure_union_null hN0 hZ0, ?_⟩
  have hxZ : ∀ x : ((N ∪ Z)ᶜ : Set X), (x : X) ∉ Z := fun x h => x.2 (Or.inr h)
  let ι : ((N ∪ Z)ᶜ : Set X) → (Nᶜ : Set X) := fun x => ⟨x.1, fun h => x.2 (Or.inl h)⟩
  have hι : Measurable ι := measurable_subtype_coe.subtype_mk
  have hmem : ∀ y : (Nᶜ : Set X), (y : X) ∉ Z → (y : X) ∈ (N ∪ Z)ᶜ := fun y hy => by
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨y.2, hy⟩
  have hTZ : ∀ x : (Nᶜ : Set X), (x : X) ∉ Z → ∀ n : ℤ, ((T.toEquiv ^ n) x : X) ∉ Z :=
    fun x hx n => hinv _ _ ((hT x _).2 ⟨n, rfl⟩) hx
  have h1 : ∀ x : ((N ∪ Z)ᶜ : Set X), (T (ι x) : X) ∉ Z := fun x => by
    simpa using hTZ (ι x) (hxZ x) 1
  have h2 : ∀ x : ((N ∪ Z)ᶜ : Set X), (T.symm (ι x) : X) ∉ Z := fun x => by
    have := hTZ (ι x) (hxZ x) (-1)
    rwa [zpow_neg, zpow_one] at this
  let T' : ((N ∪ Z)ᶜ : Set X) ≃ᵐ ((N ∪ Z)ᶜ : Set X) :=
    { toFun := fun x => ⟨T (ι x), hmem _ (h1 x)⟩
      invFun := fun x => ⟨T.symm (ι x), hmem _ (h2 x)⟩
      left_inv := fun x => Subtype.ext (by simp [ι])
      right_inv := fun x => Subtype.ext (by simp [ι])
      measurable_toFun := (measurable_subtype_coe.comp (T.measurable.comp hι)).subtype_mk
      measurable_invFun := (measurable_subtype_coe.comp (T.symm.measurable.comp hι)).subtype_mk }
  have hpow : ∀ n : ℤ, ∀ x, ι ((T'.toEquiv ^ n) x) = (T.toEquiv ^ n) (ι x) := by
    intro n
    induction n using Int.induction_on with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
      rfl
    | pred n ih =>
      intro x
      rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
      rfl
  refine ⟨T', fun x y => ?_⟩
  rw [← hagree _ _ (hxZ x) (hxZ y)]
  change ((ι x : X), (ι y : X)) ∈ E ↔ _
  rw [hT]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, Subtype.ext ?_⟩
    have := congrArg Subtype.val (hpow n x)
    rw [hn] at this
    exact this
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← hpow, hn]

/-- Homeomorphisms of the projective line act on it by evaluation. -/
abbrev mulActionHomeo : MulAction (OnePoint ℝ ≃ₜ OnePoint ℝ) (OnePoint ℝ) where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

attribute [local instance] mulActionHomeo

lemma countable_G0 : Countable G0 := by
  have : (G0 : Set (OnePoint ℝ ≃ₜ OnePoint ℝ)) = Set.range (FreeGroup.lift
      (fun x : ({a, b, c} : Set (OnePoint ℝ ≃ₜ OnePoint ℝ)) => (x : OnePoint ℝ ≃ₜ OnePoint ℝ))) := by
    rw [← MonoidHom.coe_range, ← FreeGroup.closure_eq_range]
    rfl
  exact (this ▸ Set.countable_range _ : (G0 : Set (OnePoint ℝ ≃ₜ OnePoint ℝ)).Countable).to_subtype

/-- The irrational points of the projective line. -/
def Irr : Set (OnePoint ℝ) := {x | ∃ t : ℝ, Irrational t ∧ x = (t : OnePoint ℝ)}

lemma countable_compl_Irr : (Irrᶜ : Set (OnePoint ℝ)).Countable := by
  refine ((Set.countable_range fun q : ℚ => ((q : ℝ) : OnePoint ℝ)).insert OnePoint.infty).mono ?_
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact Set.mem_insert _ _
  | coe t =>
    refine Set.mem_insert_of_mem _ ?_
    have : ¬ Irrational t := fun h => hx ⟨t, h, rfl⟩
    unfold Irrational at this
    push Not at this
    obtain ⟨q, rfl⟩ := this
    exact ⟨q, rfl⟩

theorem not_isAmenable_G0 : ¬ Garrido.IsAmenable G0 := by
  intro hA
  have := polishSpace_P1
  have := sigmaFinite_volP1
  have := countable_G0
  have hmu := isMuAmenable_orbit_of_isAmenable Monod.volP1 G0
    (fun g => (g : OnePoint ℝ ≃ₜ OnePoint ℝ).continuous.measurable) hA
  set E0 : Set (OnePoint ℝ × OnePoint ℝ) := {p | ∃ g : G0, g • p.1 = p.2}
  let Z : Set (OnePoint ℝ) := {y | ∃ x, x ∉ Irr ∧ (x, y) ∈ E0}
  have hZc : Z.Countable := by
    refine (Set.countable_iUnion fun g : G0 => countable_compl_Irr.image (fun x => g • x)).mono ?_
    rintro y ⟨x, hx, g, hg⟩
    exact Set.mem_iUnion.2 ⟨g, x, hx, hg⟩
  have hsmul : ∀ (g : G0) (x : OnePoint ℝ), g • x = (g : OnePoint ℝ ≃ₜ OnePoint ℝ) x :=
    fun _ _ => rfl
  apply (range_SL2Z_lt_K_and_dense_and_not_isMuAmenable).2.2
  refine isMuAmenable_transfer hmu Z hZc.measurableSet (volP1_countable hZc) ?_ ?_
  · rintro x y ⟨g, hg⟩ hx ⟨x', hx', h, hh⟩
    refine hx ⟨x', hx', g⁻¹ * h, ?_⟩
    simp only at hg hh ⊢
    rw [mul_smul, hh, ← hg, inv_smul_smul]
  · intro x y hx _
    have hxI : x ∈ Irr := by
      by_contra h
      exact hx ⟨x, h, 1, one_smul _ _⟩
    obtain ⟨t, ht, rfl⟩ := hxI
    have := Set.ext_iff.1 (orbit_G0_eq_orbit_K_of_irrational t ht) y
    simp only [Set.mem_ofPred_eq] at this
    simp only [E0, Set.mem_ofPred_eq, hsmul]
    rw [← this]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, g.2, hg⟩
    · rintro ⟨g, hg, h⟩
      exact ⟨⟨g, hg⟩, h⟩

theorem isFinitelyPresented_G0 : Group.IsFinitelyPresented G0 := by
  obtain ⟨e, -⟩ := exists_mulEquiv_G0_G0Seq_and_semiconj_Phi
  have := presentation_G_G0Seq_and_isFinitelyPresented.2.2.2
  exact Group.IsFinitelyPresented.equiv ((MulEquiv.inv' G0).trans e).symm

end Amen

end LodhaMoore.Dev.Top

namespace LodhaMoore

open LodhaMoore.Dev.Top

end LodhaMoore
end

section
open LodhaMoore
open LodhaMoore.Dev.Top
theorem solution :
    ¬ Garrido.IsAmenable G0 ∧ Group.IsFinitelyPresented G0 :=
  ⟨not_isAmenable_G0, isFinitelyPresented_G0⟩
end
