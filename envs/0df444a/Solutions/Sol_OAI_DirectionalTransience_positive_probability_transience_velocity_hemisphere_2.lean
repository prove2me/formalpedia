-- Prove2me | solution 2 for OAI.DirectionalTransience.positive_probability_transience_velocity_hemisphere
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:10:37.812676+00:00
-- url     : https://prove2.me/submissions/0cfe8ae5-3b5b-480d-9952-0d0da8f67126

import Mathlib
import Definitions.Def_VelocityHemisphere
import Definitions.Def_DirectionalWalk
import Theorems.Thm_OAI_DirectionalZeroOne_directional_zero_one
import Theorems.Thm_OAI_DirectionalBallisticityUnfolded_exists_velocity_of_directionally_transient

namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section X
variable {𝕜 𝕜₂ E Eₗ F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup Eₗ] [NormedSpace 𝕜 Eₗ] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F] [CompleteSpace F]

end X
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y
/-- d13f23b's `LinearIsometry.completion`: a linear isometry extends to the completions
(Kadison similarity, oaiq-075). -/
noncomputable def _root_.LinearIsometry.completion {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) :
    UniformSpace.Completion E →ₗᵢ[𝕜] UniformSpace.Completion F :=
  { toLinearMap := f.toContinuousLinearMap.completion.toLinearMap
    norm_map' := by
      intro x
      refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
      intro y
      simp }
@[simp]
theorem _root_.LinearIsometry.completion_apply_coe {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) (x : E) : f.completion (x : UniformSpace.Completion E) = (f x : UniformSpace.Completion F) :=
  ContinuousLinearMap.completion_apply_coe f.toContinuousLinearMap x
/-- Mathlib d13f23b's `Subtype.starOrderedRing`: the order a closed ⋆-subalgebra of a C⋆-algebra inherits
(Kadison similarity, oaiq-075). -/
theorem _root_.Subtype.starOrderedRing {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (S : StarSubalgebra ℂ A) [hS : IsClosed (S : Set A)] :
    StarOrderedRing S := by
  refine StarOrderedRing.of_nonneg_iff' (fun {a b} h c => ?_) (fun {s} => ?_)
  · show ((c : A) + (a : A)) ≤ (c : A) + (b : A)
    exact add_le_add le_rfl (show (a : A) ≤ (b : A) from h)
  · constructor
    · intro hs
      have hs' : (0 : A) ≤ (s : A) := hs
      have hmem : CFC.sqrt (s : A) ∈ S := by
        rw [CFC.sqrt_eq_real_sqrt _ hs']
        exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) (s := S) _ s.property
      refine ⟨⟨CFC.sqrt (s : A), hmem⟩, Subtype.ext ?_⟩
      show (s : A) = star (CFC.sqrt (s : A)) * CFC.sqrt (s : A)
      rw [CFC.sqrt_nonneg _ |>.isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ hs']
    · rintro ⟨t, rfl⟩
      show (0 : A) ≤ star (t : A) * (t : A)
      exact star_mul_self_nonneg _

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed ⋆-subalgebra of a C⋆-algebra is star ordered (d13f23b finds this by instance search). -/
instance starSubalgebraStarOrderedRing {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] : StarOrderedRing S :=
  Subtype.starOrderedRing S
instance vonNeumannAlgebraStarOrderedRing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : StarOrderedRing P :=
  Subtype.starOrderedRing P.toStarSubalgebra
/-- Mathlib d13f23b's `IsUnital`: a non-unital ring with a two-sided identity element (Kadison similarity,
oaiq-075). -/
class IsUnital (A : Type*) [NonUnitalRing A] : Prop where
  exists_one : ∃ e : A, ∀ a : A, e * a = a ∧ a * e = a

/-- d13f23b's `IsUnital.toNormedRing`: a non-unital normed ring with an identity is a normed ring. -/
@[instance_reducible]
noncomputable def IsUnital.toNormedRing {A : Type*} [NonUnitalNormedRing A] [h : IsUnital A] :
    NormedRing A :=
  let e := h.exists_one.choose
  have he := h.exists_one.choose_spec
  letI : One A := ⟨e⟩
  letI : NatCast A := ⟨Nat.unaryCast⟩
  letI : IntCast A := ⟨Int.castDef⟩
  { ‹NonUnitalNormedRing A› with
    one_mul := fun a => (he a).1
    mul_one := fun a => (he a).2
    natCast_zero := rfl
    natCast_succ := fun n => rfl
    intCast_ofNat := fun n => rfl
    intCast_negSucc := fun n => rfl }
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience














def DirectionallyTransient {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) : Prop :=
  ∀ᵐ X ∂annealedLaw ν,
    Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop

def HasVelocity {d : ℕ} (ν : Measure (Row d)) (v : Vector d) : Prop :=
  ∀ᵐ X ∂annealedLaw ν,
    Tendsto (fun n : ℕ => (fun i => (X n i : ℝ) / (n : ℝ))) atTop (𝓝 v)

open scoped ENNReal NNReal Classical Topology BigOperators

end DirectionalTransience

end OAI
end
end

section
section
namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

instance environmentLaw_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (environmentLaw ν) := by
  unfold environmentLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance initialLaw_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (initialLaw ν) := by
  unfold initialLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance annealedLaw_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (annealedLaw ν) := by
  unfold annealedLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma row_entry_le_one {d : ℕ} (p : Row d) (e : Direction d) : p.1 e ≤ 1 := by
  calc
    p.1 e ≤ ∑ i, p.1 i := Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ e)
    _ = 1 := p.2

lemma hasVelocity_unique {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {v w : Vector d} (hv : HasVelocity ν v) (hw : HasVelocity ν w) : v = w := by
  obtain ⟨X, hXv, hXw⟩ := (hv.and hw).exists
  exact tendsto_nhds_unique hXv hXw

noncomputable def stateTrajectory {d : ℕ} : Kernel (State d) (ℕ → State d) :=
  (Kernel.traj (historyTransition (d := d)) 0).comap
    (fun z _ => z) (Measurable.of_eval fun _ => measurable_id)

instance stateTrajectory_markov {d : ℕ} : IsMarkovKernel (stateTrajectory (d := d)) := by
  unfold stateTrajectory
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def quenchedKernel {d : ℕ} : Kernel (State d) (Path d) :=
  stateTrajectory.map (fun z n => (z n).2)

instance quenchedKernel_markov {d : ℕ} : IsMarkovKernel (quenchedKernel (d := d)) := by
  apply Kernel.IsMarkovKernel.map
  exact Measurable.of_eval fun n => measurable_snd.comp (measurable_pi_apply n)

lemma stateTrajectory_eq {d : ℕ} (μ : Measure (State d)) :
    stateTrajectory ∘ₘ μ = Kernel.trajMeasure μ (historyTransition (d := d)) := by
  unfold Kernel.trajMeasure stateTrajectory
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  rfl

lemma annealed_eq_quenched_mixture {d : ℕ} (ν : Measure (Row d)) :
    annealedLaw ν = quenchedKernel ∘ₘ initialLaw ν := by
  unfold annealedLaw quenchedKernel
  rw [← stateTrajectory_eq, Measure.map_comp]
  exact Measurable.of_eval fun n => measurable_snd.comp (measurable_pi_apply n)

lemma annealed_apply {d : ℕ} (ν : Measure (Row d)) {A : Set (Path d)}
    (hA : MeasurableSet A) :
    annealedLaw ν A = ∫⁻ ω, quenchedKernel (ω, (0 : Lattice d)) A ∂environmentLaw ν := by
  rw [annealed_eq_quenched_mixture, Measure.bind_apply hA (Kernel.aemeasurable _),
    initialLaw, lintegral_map]
  · exact Kernel.measurable_coe _ hA
  · exact measurable_id.prodMk measurable_const

lemma stateTrajectory_initial {d : ℕ} (z : State d) :
    (stateTrajectory z).map (fun X => X 0) = Measure.dirac z := by
  rw [stateTrajectory, Kernel.comap_apply]
  have h := Kernel.traj_map_frestrictLe_apply (X := fun _ => State d)
    (κ := historyTransition (d := d))
    0 0 (fun _ => z)
  rw [Kernel.partialTraj_self, Kernel.id_apply] at h
  have hm : Measurable (fun X : (i : Finset.Iic 0) → State d =>
      X ⟨0, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  have := congrArg (fun μ => μ.map
    (fun X : (i : Finset.Iic 0) → State d => X ⟨0, Finset.mem_Iic.mpr le_rfl⟩)) h
  rw [Measure.map_map hm (Preorder.measurable_frestrictLe 0), Measure.map_dirac' hm] at this
  exact this

lemma quenched_initial {d : ℕ} (z : State d) :
    (quenchedKernel z).map (fun X => X 0) = Measure.dirac z.2 := by
  have hm : Measurable (fun z : ℕ → State d => fun n => (z n).2) := by fun_prop
  rw [quenchedKernel, Kernel.map_apply _ hm, Measure.map_map (measurable_pi_apply 0) hm]
  have h := congrArg (fun μ => μ.map Prod.snd) (stateTrajectory_initial z)
  rw [Measure.map_map measurable_snd (measurable_pi_apply 0),
    Measure.map_dirac' measurable_snd] at h
  exact h

lemma quenched_initial_ae {d : ℕ} (z : State d) :
    ∀ᵐ X ∂quenchedKernel z, X 0 = z.2 := by
  have h : ∀ᵐ x ∂(quenchedKernel z).map (fun X => X 0), x = z.2 := by
    rw [quenched_initial]
    exact ae_dirac_iff (measurableSet_singleton _ ) |>.mpr rfl
  exact (ae_map_iff (measurable_pi_apply 0).aemeasurable
    (measurableSet_singleton _)).mp h

instance state_measurableEq {d : ℕ} : MeasurableEq (State d) where
  measurableSet_diagonal := by
    change MeasurableSet {zz : State d × State d | zz.1 = zz.2}
    simp only [Prod.ext_iff, Set.ofPred_and]
    exact (measurableSet_eq_fun (measurable_fst.comp measurable_fst)
      (measurable_fst.comp measurable_snd)).inter
      (measurableSet_eq_fun (measurable_snd.comp measurable_fst)
        (measurable_snd.comp measurable_snd))

instance state_measurableSingleton {d : ℕ} : MeasurableSingletonClass (State d) := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def AdmissibleStep {d : ℕ} (z z' : State d) : Prop :=
  ∃ e : Direction d, z' = (z.1, z.2 + step e)

lemma measurableSet_admissibleStep {d : ℕ} :
    MeasurableSet {zz : State d × State d | AdmissibleStep zz.1 zz.2} := by
  simp only [AdmissibleStep, Prod.ext_iff, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro e
  exact (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
    (measurable_fst.comp measurable_fst)).inter
    (measurableSet_eq_fun (measurable_snd.comp measurable_snd)
      ((measurable_snd.comp measurable_fst).add_const (step e)))

lemma transition_admissible {d : ℕ} (z : State d) :
    ∀ᵐ z' ∂transition z, AdmissibleStep z z' := by
  change ∀ᵐ z' ∂∑ e : Direction d,
    ((z.1 z.2).1 e : ℝ≥0∞) • Measure.dirac (z.1, z.2 + step e), AdmissibleStep z z'
  apply ae_finsetSum_measure_iff.mpr
  intro e _
  apply Measure.ae_smul_measure
  apply (ae_dirac_iff _).mpr
  · exact ⟨e, rfl⟩
  · exact measurableSet_admissibleStep.preimage (measurable_const.prodMk measurable_id)

lemma stateTrajectory_admissible {d : ℕ} (z : State d) :
    ∀ᵐ X ∂stateTrajectory z, ∀ n, AdmissibleStep (X n) (X (n + 1)) := by
  rw [stateTrajectory, Kernel.comap_apply]
  apply ae_all_iff.mpr
  intro n
  let p := fun zz : ((i : Finset.Iic n) → State d) × State d =>
    AdmissibleStep (zz.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) zz.2
  have hm : Measurable (fun zz : ((i : Finset.Iic n) → State d) × State d =>
      (zz.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩, zz.2)) := by fun_prop
  have hp : MeasurableSet {zz | p zz} :=
    measurableSet_admissibleStep.preimage hm
  have h : ∀ᵐ zz ∂(Kernel.partialTraj (X := fun _ => State d) (historyTransition (d := d)) 0 n (fun _ => z))
      ⊗ₘ historyTransition (d := d) n, p zz := by
    apply Measure.ae_compProd_of_ae_ae hp
    exact ae_of_all _ fun x => transition_admissible _
  rw [Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n)] at h
  exact (ae_map_iff (by fun_prop) hp).mp h

lemma stateTrajectory_environment {d : ℕ} (z : State d) :
    ∀ᵐ X ∂stateTrajectory z, ∀ n, (X n).1 = z.1 := by
  have h0 : ∀ᵐ X ∂stateTrajectory z, X 0 = z := by
    have h : ∀ᵐ y ∂(stateTrajectory z).map (fun X => X 0), y = z := by
      rw [stateTrajectory_initial]
      exact (ae_dirac_iff (measurableSet_singleton _)).mpr rfl
    exact (ae_map_iff (measurable_pi_apply 0).aemeasurable
      (measurableSet_singleton _)).mp h
  filter_upwards [h0, stateTrajectory_admissible z] with X hX hstep n
  induction n with
  | zero => rw [hX]
  | succ n ih =>
    obtain ⟨e, he⟩ := hstep n
    rw [he]
    exact ih

def stateCylinder {d : ℕ} (f : ℕ → State d) (n : ℕ) : Set (ℕ → State d) :=
  {X | ∀ i ≤ n, X i = f i}

lemma stateCylinder_eq_preimage {d : ℕ} (f : ℕ → State d) (n : ℕ) :
    stateCylinder f n = (fun X : ℕ → State d => Preorder.frestrictLe n X) ⁻¹' {fun i : Finset.Iic n => f i} := by
  ext X
  simp only [stateCylinder, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    exact h i (Finset.mem_Iic.mp i.2)
  · intro h i hi
    exact congrFun h ⟨i, Finset.mem_Iic.mpr hi⟩

lemma stateTrajectory_cylinder_succ {d : ℕ} (z : State d) (f : ℕ → State d) (n : ℕ) :
    stateTrajectory z (stateCylinder f (n + 1)) =
      transition (f n) {f (n + 1)} * stateTrajectory z (stateCylinder f n) := by
  rw [stateTrajectory, Kernel.comap_apply]
  have h := Kernel.partialTraj_compProd_eq_map_traj (X := fun _ => State d)
    (κ := historyTransition (d := d)) (x₀ := fun _ => z) (Nat.zero_le n)
  have hm : Measurable (fun X : ℕ → State d => (Preorder.frestrictLe n X, X (n + 1))) := by
    fun_prop
  have he : (fun X : ℕ → State d => (Preorder.frestrictLe n X, X (n + 1))) ⁻¹'
      ({fun i : Finset.Iic n => f i} ×ˢ {f (n + 1)}) = stateCylinder f (n + 1) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
      stateCylinder, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h₁, h₂⟩ i hi
      obtain hi | rfl := Nat.lt_or_eq_of_le hi
      · exact congrFun h₁ ⟨i, Finset.mem_Iic.mpr (by omega)⟩
      · exact h₂
    · intro hX
      exact ⟨funext fun i => hX i (by have := Finset.mem_Iic.mp i.2; omega), hX _ le_rfl⟩
  have hs := congrArg (fun μ : Measure (((i : Finset.Iic n) → State d) × State d) =>
    μ ({fun i : Finset.Iic n => f i} ×ˢ {f (n + 1)})) h
  rw [Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton, Measure.map_apply hm
      ((measurableSet_singleton _).prod (measurableSet_singleton _)), he] at hs
  rw [← hs]
  congr 1
  rw [stateCylinder_eq_preimage, ← Measure.map_apply (Preorder.measurable_frestrictLe n)
    (measurableSet_singleton _), Kernel.traj_map_frestrictLe_apply]

lemma stateTrajectory_cylinder {d : ℕ} (z : State d) (f : ℕ → State d)
    (hf : f 0 = z) (n : ℕ) :
    stateTrajectory z (stateCylinder f n) =
      ∏ i ∈ Finset.range n, transition (f i) {f (i + 1)} := by
  induction n with
  | zero =>
    have he : stateCylinder f 0 = (fun X : ℕ → State d => X 0) ⁻¹' {z} := by
      ext X
      simp [stateCylinder, hf]
    rw [he, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton _),
      stateTrajectory_initial]
    simp
  | succ n ih =>
    rw [stateTrajectory_cylinder_succ, ih, Finset.prod_range_succ, mul_comm]

end DirectionalTransience
end
end

end OAI
end
end

section
section
namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def wordPath {d : ℕ} (x : Lattice d) : List (Direction d) → Path d
  | [], _ => x
  | _ :: _, 0 => x
  | e :: w, n + 1 => wordPath (x + step e) w n

@[simp] lemma wordPath_zero {d : ℕ} (x : Lattice d) (w : List (Direction d)) :
    wordPath x w 0 = x := by cases w <;> rfl

def pathCylinder {d : ℕ} (f : Path d) (n : ℕ) : Set (Path d) :=
  {X | ∀ i ≤ n, X i = f i}

lemma measurableSet_pathCylinder {d : ℕ} (f : Path d) (n : ℕ) :
    MeasurableSet (pathCylinder f n) := by
  simp only [pathCylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_eq_fun (measurable_pi_apply i : Measurable (fun X : Path d => X i))
      measurable_const

lemma pathMeasure_ext {d : ℕ} (μ ν : Measure (Path d)) [IsFiniteMeasure μ]
    (h : ∀ f n, μ (pathCylinder f n) = ν (pathCylinder f n)) : μ = ν := by
  let P : (I : Finset ℕ) → Measure ((i : I) → Lattice d) :=
    fun I => μ.map I.restrict
  have hp : IsProjectiveMeasureFamily (α := fun _ : ℕ => Lattice d) P := by
    exact isProjectiveMeasureFamily_map_restrict (P := μ) (X := fun n (X : Path d) => X n)
      (fun n => (measurable_pi_apply n).aemeasurable)
  have hμ : IsProjectiveLimit (α := fun _ : ℕ => Lattice d) μ P := by
    intro I
    rfl
  apply hμ.unique
  apply (isProjectiveLimit_nat_iff hp ν).mpr
  intro n
  apply Measure.ext_of_singleton
  intro f
  have hf : MeasurableSet ({f} : Set ((i : Finset.Iic n) → Lattice d)) :=
    measurableSet_singleton _
  rw [Measure.map_apply (Preorder.measurable_frestrictLe n) hf]
  change _ = μ.map (Preorder.frestrictLe n) {f}
  rw [Measure.map_apply (Preorder.measurable_frestrictLe n) hf]
  let g : Path d := fun i => if hi : i ≤ n then f ⟨i, Finset.mem_Iic.mpr hi⟩ else 0
  have he : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f} = pathCylinder g n := by
    ext X
    simp only [Set.mem_preimage, Set.mem_singleton_iff, pathCylinder, Set.mem_ofPred_eq]
    constructor
    · intro hh i hi
      simpa [g, hi] using congrFun hh ⟨i, Finset.mem_Iic.mpr hi⟩
    · intro hh
      funext i
      simpa [g, Finset.mem_Iic.mp i.2] using hh i (Finset.mem_Iic.mp i.2)
  rw [he, h]

noncomputable def edgeWeight {d : ℕ} (ω : Environment d) (x y : Lattice d) : ℝ≥0∞ :=
  ∑ e : Direction d, if y = x + step e then ((ω x).1 e : ℝ≥0∞) else 0

lemma transition_singleton {d : ℕ} (ω : Environment d) (x y : Lattice d) :
    transition (ω, x) {(ω, y)} = edgeWeight ω x y := by
  classical
  change (∑ e : Direction d, ((ω x).1 e : ℝ≥0∞) •
    Measure.dirac (ω, x + step e)) {(ω, y)} = _
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, edgeWeight]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : y = x + step e
  · simp [he]
  · simp [he, Ne.symm he]

lemma quenched_pathCylinder {d : ℕ} (ω : Environment d) (x : Lattice d)
    (f : Path d) (hf : f 0 = x) (n : ℕ) :
    quenchedKernel (ω, x) (pathCylinder f n) =
      ∏ i ∈ Finset.range n, edgeWeight ω (f i) (f (i + 1)) := by
  have hm : Measurable (fun z : ℕ → State d => fun n => (z n).2) := by fun_prop
  rw [quenchedKernel, Kernel.map_apply _ hm, Measure.map_apply hm (measurableSet_pathCylinder f n)]
  have he : (fun z : ℕ → State d => fun n => (z n).2) ⁻¹' pathCylinder f n
      =ᵐ[stateTrajectory (ω, x)] stateCylinder (fun i => (ω, f i)) n := by
    filter_upwards [stateTrajectory_environment (ω, x)] with X hX
    apply propext
    change (∀ i ≤ n, (X i).2 = f i) ↔ (∀ i ≤ n, X i = (ω, f i))
    constructor
    · intro hh i hi
      exact Prod.ext (hX i) (hh i hi)
    · intro hh i hi
      exact congrArg Prod.snd (hh i hi)
  rw [measure_congr he, stateTrajectory_cylinder _ _ (by simp [hf])]
  simp only [transition_singleton]

lemma quenched_pathCylinder_zero {d : ℕ} (ω : Environment d) (x : Lattice d)
    (f : Path d) (hf : f 0 ≠ x) (n : ℕ) :
    quenchedKernel (ω, x) (pathCylinder f n) = 0 := by
  have hsub : pathCylinder f n ⊆ {X | X 0 ≠ x} := by
    intro X hX
    change X 0 ≠ x
    rw [hX 0 (Nat.zero_le n)]
    exact hf
  exact measure_mono_null hsub ((ae_iff).mp (quenched_initial_ae (ω, x)))

end DirectionalTransience
end
end

end OAI
end
end

section
section
namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

end DirectionalTransience
end
end

end OAI
end
end

section
section
namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience


lemma measurableSet_transientPaths {d : ℕ} (ℓ : Vector d) :
    MeasurableSet (TransientPaths ℓ) := by
  apply measurableSet_tendsto
  intro n
  exact (measurable_of_countable (fun y : Lattice d => dot (realPosition y) ℓ)).comp
    (measurable_pi_apply n)

end DirectionalTransience
end
end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne















lemma probabilityMeasure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → β}
    (hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) :=
  (Measure.isProbabilityMeasure_map_iff hf).2 inferInstance

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (environmentLaw μ) := by
  unfold environmentLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (initialLaw μ x) := by
  apply probabilityMeasure_map
  exact (measurable_id.prodMk measurable_const).aemeasurable

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (annealed μ x) := by
  apply probabilityMeasure_map
  exact (Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n))).aemeasurable

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

noncomputable def walkInitialLaw {d : ℕ} (μ : Measure (Environment d)) (x : Site d) :
    Measure (State d) := μ.map (fun ω => (ω, x))

instance {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (walkInitialLaw μ x) := by
  apply probabilityMeasure_map
  exact (measurable_id.prodMk measurable_const).aemeasurable

noncomputable def walkStateLaw {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) : Measure (ℕ → State d) :=
  Kernel.trajMeasure (X := fun _ => State d) (walkInitialLaw μ x) (historyKernel d)

instance {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (walkStateLaw μ x) := by
  unfold walkStateLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma lintegral_transition {d : ℕ} (s : State d) (f : State d → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ t, f t ∂transition d s) =
      ∑ e, ENNReal.ofReal ((s.1 s.2).val e) * f (s.1, s.2 + stepVector e) := by
  change (∫⁻ t, f t ∂∑ e : Step d,
    ENNReal.ofReal ((s.1 s.2).val e) • Measure.dirac (s.1, s.2 + stepVector e)) = _
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

lemma walkStateLaw_initial_history {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) :
    (walkStateLaw μ x).map (Preorder.frestrictLe 0) =
      (walkInitialLaw μ x).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => State d)).symm := by
  rw [walkStateLaw, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe _),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]

lemma walkStateLaw_initial {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) : (walkStateLaw μ x).map (fun z => z 0) = walkInitialLaw μ x := by
  let e := MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => State d)
  have h : (fun z : ℕ → State d => z 0) = e ∘ Preorder.frestrictLe 0 := by
    funext z
    rfl
  rw [h, ← Measure.map_map e.measurable (measurable_frestrictLe 0), walkStateLaw_initial_history]
  exact e.symm.map_symm_map

lemma walkStateLaw_one_step {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ)
    (f : ((i : Finset.Iic n) → State d) × State d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f (Preorder.frestrictLe n z, z (n + 1)) ∂walkStateLaw μ x) =
      ∫⁻ z, ∫⁻ t, f (Preorder.frestrictLe n z, t) ∂transition d (z n) ∂walkStateLaw μ x := by
  have hm : Measurable (fun z : ℕ → State d => (Preorder.frestrictLe n z, z (n+1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply _)
  rw [← lintegral_map hf hm]
  unfold walkStateLaw
  rw [← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.lintegral_compProd hf]
  rw [lintegral_map]
  · rfl
  · exact hf.lintegral_kernel_prod_right'
  · exact measurable_frestrictLe n

noncomputable def entryWeight {d : ℕ} (ω : Environment d) (x y : Site d) : ℝ≥0∞ :=
  ∑ e : Step d, if x + stepVector e = y then ENNReal.ofReal ((ω x).val e) else 0

lemma measurable_entryWeight {d : ℕ} (x y : Site d) :
    Measurable (fun ω : Environment d => entryWeight ω x y) := by
  apply Finset.measurable_sum
  intro e he
  split_ifs
  · exact ((measurable_pi_apply e).comp
      (measurable_subtype_coe.comp (measurable_pi_apply x))).ennreal_ofReal
  · exact measurable_const

def prefixMatches {d : ℕ} (n : ℕ) (γ : ℕ → Site d) (z : ℕ → State d) : Prop :=
  ∀ i ≤ n, (z i).2 = γ i

noncomputable def prefixObservable {d : ℕ} (n : ℕ) (γ : ℕ → Site d)
    (f : Environment d → ℝ≥0∞) (z : ℕ → State d) : ℝ≥0∞ := by
  classical
  exact if prefixMatches n γ z then f (z n).1 else 0

lemma measurableSet_prefixMatches {d : ℕ} (n : ℕ) (γ : ℕ → Site d) :
    MeasurableSet {z : ℕ → State d | prefixMatches n γ z} := by
  simp only [prefixMatches, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_snd.comp (measurable_pi_apply i)) measurable_const))

lemma prefixMatches_succ {d : ℕ} (n : ℕ) (γ : ℕ → Site d) (z : ℕ → State d) :
    prefixMatches (n+1) γ z ↔ prefixMatches n γ z ∧ (z (n+1)).2 = γ (n+1) := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h _ le_rfl⟩
  · rintro ⟨h, hn⟩ i hi
    by_cases hin : i ≤ n
    · exact h i hin
    · have hie : i = n+1 := by omega
      simpa only [hie] using hn

noncomputable def pathWeight {d : ℕ} (n : ℕ) (γ : ℕ → Site d)
    (ω : Environment d) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range n, entryWeight ω (γ i) (γ (i+1))

lemma measurable_pathWeight {d : ℕ} (n : ℕ) (γ : ℕ → Site d) :
    Measurable (pathWeight n γ) := by
  exact Finset.measurable_prod _ (fun i _ => measurable_entryWeight (γ i) (γ (i+1)))

lemma pathWeight_succ {d : ℕ} (n : ℕ) (γ : ℕ → Site d) (ω : Environment d) :
    pathWeight (n+1) γ ω = pathWeight n γ ω * entryWeight ω (γ n) (γ (n+1)) :=
  Finset.prod_range_succ _ n

lemma history_matches_iff {d : ℕ} (n : ℕ) (γ : ℕ → Site d) (z : ℕ → State d) :
    (∀ i : Finset.Iic n, (frestrictLe n z i).2 = γ i) ↔ prefixMatches n γ z := by
  constructor
  · intro h i hi
    exact h ⟨i, Finset.mem_Iic.mpr hi⟩
  · intro h i
    exact h i (Finset.mem_Iic.mp i.property)

lemma prefix_lintegral_succ {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : ℕ → Site d) (f : Environment d → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z, prefixObservable (n+1) γ f z ∂walkStateLaw μ x) =
      ∫⁻ z, prefixObservable n γ (fun ω => entryWeight ω (γ n) (γ (n+1)) * f ω) z
        ∂walkStateLaw μ x := by
  classical
  let F : ((i : Finset.Iic n) → State d) × State d → ℝ≥0∞ := fun q =>
    if (∀ i, (q.1 i).2 = γ i) then
      if q.2.2 = γ (n+1) then f q.2.1 else 0
    else 0
  have hm : MeasurableSet {q : ((i : Finset.Iic n) → State d) × State d |
      ∀ i, (q.1 i).2 = γ i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_eq_fun
      (measurable_snd.comp ((measurable_pi_apply i).comp measurable_fst)) measurable_const)
  have hn : MeasurableSet {q : ((i : Finset.Iic n) → State d) × State d |
      q.2.2 = γ (n+1)} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  have hF : Measurable F :=
    Measurable.ite hm (Measurable.ite hn
      (hf.comp (measurable_fst.comp measurable_snd)) measurable_const) measurable_const
  have hFeq (z : ℕ → State d) :
      F (frestrictLe n z, z (n+1)) = prefixObservable (n+1) γ f z := by
    simp only [F, history_matches_iff, prefixObservable, prefixMatches_succ]
    split_ifs <;> simp_all
  calc
    (∫⁻ z, prefixObservable (n+1) γ f z ∂walkStateLaw μ x) =
        ∫⁻ z, F (frestrictLe n z, z (n+1)) ∂walkStateLaw μ x :=
      lintegral_congr (fun z => (hFeq z).symm)
    _ = ∫⁻ z, ∫⁻ t, F (frestrictLe n z, t) ∂transition d (z n) ∂walkStateLaw μ x :=
      walkStateLaw_one_step μ x n F hF
    _ = _ := by
      apply lintegral_congr
      intro z
      rw [lintegral_transition (z n) (fun t => F (frestrictLe n z, t))
        (hF.comp (measurable_const.prodMk measurable_id))]
      by_cases hz : prefixMatches n γ z
      · have hzn := hz n le_rfl
        simp only [F, history_matches_iff, hz, ite_true, if_true, prefixObservable]
        rw [hzn, entryWeight, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> simp_all
      · simp only [F, history_matches_iff, hz, ite_false, if_false, prefixObservable, mul_zero,
          Finset.sum_const_zero]

lemma prefix_lintegral_zero {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (γ : ℕ → Site d) (f : Environment d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, prefixObservable 0 γ f z ∂walkStateLaw μ x) =
      if x = γ 0 then ∫⁻ ω, f ω ∂μ else 0 := by
  classical
  let g : State d → ℝ≥0∞ := fun s => if s.2 = γ 0 then f s.1 else 0
  have hg : Measurable g := Measurable.ite
    (measurableSet_eq_fun measurable_snd measurable_const) (hf.comp measurable_fst) measurable_const
  have heq : prefixObservable 0 γ f = fun z => g (z 0) := by
    funext z
    simp [prefixObservable, prefixMatches, g]
  rw [heq, ← lintegral_map hg (measurable_pi_apply 0), walkStateLaw_initial,
    walkInitialLaw, lintegral_map (g := fun ω : Environment d => (ω, x)) hg
      (measurable_id.prodMk measurable_const)]
  by_cases hx : x = γ 0 <;> simp [g, hx]

lemma prefix_lintegral {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : ℕ → Site d) (f : Environment d → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z, prefixObservable n γ f z ∂walkStateLaw μ x) =
      if x = γ 0 then ∫⁻ ω, pathWeight n γ ω * f ω ∂μ else 0 := by
  induction n generalizing f with
  | zero => simpa [pathWeight] using prefix_lintegral_zero μ x γ f hf
  | succ n ih =>
    rw [prefix_lintegral_succ μ x n γ f hf,
      ih (fun ω => entryWeight ω (γ n) (γ (n+1)) * f ω)
        ((measurable_entryWeight (γ n) (γ (n+1))).mul hf)]
    simp only [pathWeight_succ, mul_assoc]

noncomputable def walkLaw {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) : Measure (Path d) := (walkStateLaw μ x).map (fun z n => (z n).2)

instance {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (walkLaw μ x) := by
  apply probabilityMeasure_map
  exact (Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n))).aemeasurable

def pathCylinder {d : ℕ} (n : ℕ) (γ : ℕ → Site d) : Set (Path d) :=
  {X | ∀ i ≤ n, X i = γ i}

lemma measurableSet_pathCylinder {d : ℕ} (n : ℕ) (γ : ℕ → Site d) :
    MeasurableSet (pathCylinder n γ) := by
  simp only [pathCylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_pi_apply i) measurable_const))

lemma walkLaw_cylinder {d : ℕ} (μ : Measure (Environment d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : ℕ → Site d) :
    walkLaw μ x (pathCylinder n γ) =
      if x = γ 0 then ∫⁻ ω, pathWeight n γ ω ∂μ else 0 := by
  classical
  have hp := prefix_lintegral μ x n γ (fun _ => 1) measurable_const
  have hobs : prefixObservable n γ (fun _ => 1) =
      {z : ℕ → State d | prefixMatches n γ z}.indicator (fun _ => 1) := by
    funext z
    simp [prefixObservable, Set.indicator]
  rw [hobs] at hp
  change (∫⁻ z, {z' : ℕ → State d | prefixMatches n γ z'}.indicator 1 z
    ∂walkStateLaw μ x) = _ at hp
  rw [lintegral_indicator_one (measurableSet_prefixMatches n γ)] at hp
  rw [walkLaw, Measure.map_apply (f := fun z : ℕ → State d => fun n => (z n).2)
    (Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n)))
    (measurableSet_pathCylinder n γ)]
  simpa only [pathCylinder, prefixMatches, Set.preimage_ofPred_eq, mul_one] using hp

lemma annealed_cylinder {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (n : ℕ) (γ : ℕ → Site d) :
    annealed μ x (pathCylinder n γ) =
      if x = γ 0 then ∫⁻ ω, pathWeight n γ ω ∂environmentLaw μ else 0 :=
  walkLaw_cylinder (environmentLaw μ) x n γ

noncomputable def quenchedKernel (d : ℕ) : Kernel (State d) (Path d) :=
  ((Kernel.traj (X := fun _ => State d) (historyKernel d) 0).comap
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => State d)).symm
    (MeasurableEquiv.measurable _)).map (fun z n => (z n).2)

instance (d : ℕ) : IsMarkovKernel (quenchedKernel d) := by
  unfold quenchedKernel
  apply Kernel.IsMarkovKernel.map
  exact Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n))

end DirectionalZeroOne

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology


namespace DirectionalTransience

lemma measurableSet_velocityPaths {d : ℕ} (v : Vector d) : MeasurableSet (VelocityPaths v) := by
  apply measurableSet_tendsto
  intro n
  exact (measurable_of_countable (fun y : Lattice d => fun i => (y i:ℝ)/(n:ℝ))).comp
    (measurable_pi_apply n)

lemma velocityPaths_projection {d : ℕ} (v ℓ : Vector d) (X : Path d)
    (hX : X ∈ VelocityPaths v) :
    Tendsto (fun n : ℕ => dot (realPosition (X n)) ℓ/(n:ℝ)) atTop (𝓝 (dot v ℓ)) := by
  have hh := tendsto_finsetSum Finset.univ (fun i _ =>
    (tendsto_pi_nhds.mp hX i).mul_const (ℓ i))
  simpa only [dot,realPosition,Finset.sum_div,div_mul_eq_mul_div] using hh

theorem directional_transience_implies_ballisticity_unit {d : ℕ} (hd : 2 ≤ d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : dot ℓ ℓ=1) (htrans : DirectionallyTransient ν ℓ) :
    ∃ v : Vector d, 0 < dot v ℓ ∧ HasVelocity ν v :=
  OAI.DirectionalBallisticityUnfolded.exists_velocity_of_directionally_transient hd ν hue ℓ hℓ transition (fun z => rfl)
    (annealedLaw ν) rfl htrans

end DirectionalTransience
end OAI


namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

namespace RowBridge

def toReal {d : ℕ} (p : Row d) : DirectionalZeroOne.Row d :=
  ⟨fun e => (p.1 e : ℝ), by
    constructor
    · intro e
      exact ⟨(p.1 e).coe_nonneg, by exact_mod_cast row_entry_le_one p e⟩
    · change ∑ e : Direction d, (p.1 e : ℝ) = 1
      rw [← NNReal.coe_sum, p.2]
      rfl⟩

lemma measurable_toReal {d : ℕ} : Measurable (toReal (d := d)) := by
  apply Measurable.subtype_mk
  exact Measurable.of_eval fun e =>
    ((measurable_pi_apply e).comp measurable_subtype_coe).coe_nnreal_real

noncomputable def rowLaw {d : ℕ} (ν : Measure (Row d)) :
    Measure (DirectionalZeroOne.Row d) := ν.map toReal

instance rowLaw_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (rowLaw ν) :=
  (Measure.isProbabilityMeasure_map_iff measurable_toReal.aemeasurable).2 inferInstance

def environment {d : ℕ} (ω : Environment d) : DirectionalZeroOne.Environment d :=
  fun x => toReal (ω x)

lemma measurable_environment {d : ℕ} : Measurable (environment (d := d)) :=
  Measurable.of_eval fun x => measurable_toReal.comp (measurable_pi_apply x)

lemma environmentLaw_map {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    (environmentLaw ν).map environment = DirectionalZeroOne.environmentLaw (rowLaw ν) := by
  exact Measure.infinitePi_map_pi (fun _ : Lattice d => ν) (fun _ => measurable_toReal)

lemma strictEllipticity {d : ℕ} (ν : Measure (Row d)) (hue : UniformElliptic ν) :
    DirectionalZeroOne.StrictEllipticity (rowLaw ν) := by
  obtain ⟨κ, hκ, hrows⟩ := hue
  have hm : MeasurableSet {p : DirectionalZeroOne.Row d | ∀ e, 0 < p.1 e} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun e => measurableSet_lt measurable_const
      ((measurable_pi_apply e).comp (measurable_subtype_coe :
        Measurable (fun p : DirectionalZeroOne.Row d => p.1)))
  apply (ae_map_iff measurable_toReal.aemeasurable hm).mpr
  filter_upwards [hrows] with p hp e
  change (0 : ℝ) < (p.1 e : ℝ)
  exact_mod_cast lt_of_lt_of_le hκ (hp e)

lemma entryWeight {d : ℕ} (ω : Environment d) (x y : Lattice d) :
    DirectionalZeroOne.entryWeight (environment ω) x y = edgeWeight ω x y := by
  classical
  simp only [DirectionalZeroOne.entryWeight, edgeWeight,
    environment, toReal, ENNReal.ofReal_coe_nnreal]
  apply Finset.sum_congr rfl
  intro e _
  change (if x + step e = y then ((ω x).1 e : ℝ≥0∞) else 0) = _
  simp only [eq_comm]

lemma annealedLaw_eq {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    annealedLaw ν = DirectionalZeroOne.annealed (rowLaw ν) 0 := by
  apply pathMeasure_ext
  intro γ n
  rw [annealed_apply ν (measurableSet_pathCylinder γ n)]
  change (∫⁻ ω, quenchedKernel (ω, 0) (pathCylinder γ n) ∂environmentLaw ν) =
    DirectionalZeroOne.annealed (rowLaw ν) 0 (DirectionalZeroOne.pathCylinder n γ)
  rw [DirectionalZeroOne.annealed_cylinder]
  by_cases h0 : γ 0 = 0
  · rw [ite_eq_left h0.symm, ← environmentLaw_map ν,
      lintegral_map (DirectionalZeroOne.measurable_pathWeight n γ) measurable_environment]
    apply lintegral_congr
    intro ω
    rw [quenched_pathCylinder ω 0 γ h0 n]
    simp only [DirectionalZeroOne.pathWeight, entryWeight]
  · rw [ite_eq_right (Ne.symm h0)]
    simp only [quenched_pathCylinder_zero _ _ _ h0, lintegral_zero]

end RowBridge

end DirectionalTransience

end OAI


namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

lemma uniformElliptic_directional_zero_one {d : ℕ} (hd : 3 ≤ d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : ℓ ≠ 0) :
    annealedLaw ν (TransientPaths ℓ) = 0 ∨ annealedLaw ν (TransientPaths ℓ) = 1 := by
  have h := DirectionalZeroOne.directional_zero_one d hd (RowBridge.rowLaw ν)
    (RowBridge.strictEllipticity ν hue) ℓ hℓ
  change DirectionalZeroOne.annealed (RowBridge.rowLaw ν) 0 (TransientPaths ℓ) = 0 ∨
    DirectionalZeroOne.annealed (RowBridge.rowLaw ν) 0 (TransientPaths ℓ) = 1 at h
  rwa [← RowBridge.annealedLaw_eq ν] at h

lemma dot_div_right {d : ℕ} (v ℓ : Vector d) (r : ℝ) :
    dot v (fun i => ℓ i / r) = dot v ℓ / r := by
  simp only [dot, mul_div_assoc, Finset.sum_div]

lemma dot_self_pos_of_ne_zero {d : ℕ} (ℓ : Vector d) (hℓ : ℓ ≠ 0) :
    0 < dot ℓ ℓ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hℓ
  change ℓ i ≠ 0 at hi
  exact (mul_self_pos.mpr hi).trans_le
    (Finset.single_le_sum (fun j _ => mul_self_nonneg (ℓ j)) (Finset.mem_univ i))

lemma transientPaths_div_pos {d : ℕ} (ℓ : Vector d) {r : ℝ} (hr : 0 < r) :
    TransientPaths (fun i => ℓ i / r) = TransientPaths ℓ := by
  ext X
  simp only [TransientPaths, Set.mem_ofPred_eq, dot_div_right]
  exact tendsto_div_const_atTop_of_pos hr

lemma velocity_of_positive_escape {d : ℕ} (hd : 3 ≤ d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : ℓ ≠ 0) (hpos : 0 < annealedLaw ν (TransientPaths ℓ)) :
    ∃ v : Vector d, 0 < dot v ℓ ∧ HasVelocity ν v := by
  have hprob : annealedLaw ν (TransientPaths ℓ) = 1 :=
    (uniformElliptic_directional_zero_one hd ν hue ℓ hℓ).resolve_left hpos.ne'
  have hs : 0 < dot ℓ ℓ := dot_self_pos_of_ne_zero ℓ hℓ
  let r : ℝ := Real.sqrt (dot ℓ ℓ)
  have hr : 0 < r := Real.sqrt_pos.mpr hs
  let u : Vector d := fun i => ℓ i / r
  have hu : dot u u = 1 := by
    have he : dot u u = dot ℓ ℓ / (r * r) := by
      simp only [u, dot, div_mul_div_comm, Finset.sum_div]
    rw [he, show r * r = dot ℓ ℓ from Real.mul_self_sqrt hs.le, div_self hs.ne']
  have htrans : DirectionallyTransient ν u := by
    apply (mem_ae_iff_prob_eq_one (measurableSet_transientPaths u)).mpr
    rw [transientPaths_div_pos ℓ hr]
    exact hprob
  obtain ⟨v, hvu, hv⟩ := directional_transience_implies_ballisticity_unit
    (by omega : 2 ≤ d) ν hue u hu htrans
  refine ⟨v, ?_, hv⟩
  have hp : 0 < dot v ℓ / r := by simpa only [u, dot_div_right] using hvu
  exact (div_pos_iff_of_pos_right hr).mp hp

lemma escape_probability_one_of_velocity {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (v u : Vector d) (hv : HasVelocity ν v)
    (hvu : 0 < dot v u) : annealedLaw ν (TransientPaths u) = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_transientPaths u)).mp
  filter_upwards [hv] with X hX
  have hproj := velocityPaths_projection v u X hX
  have hprod := hproj.pos_mul_atTop hvu
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

lemma unit_direction_ne_zero {d : ℕ} (u : Vector d) (hu : dot u u = 1) : u ≠ 0 := by
  intro h
  subst u
  simp [dot] at hu

end DirectionalTransience

end OAI


namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

theorem positive_probability_transience_velocity_hemisphere_oai
    {d : ℕ} (hd : 3 ≤ d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : ℓ ≠ 0)
    (hpos : 0 < annealedLaw ν (TransientPaths ℓ)) :
    ∃ v : Vector d,
      v ≠ 0 ∧ 0 < dot v ℓ ∧ annealedLaw ν (VelocityPaths v) = 1 ∧
      (∀ w : Vector d, annealedLaw ν (VelocityPaths w) = 1 → w = v) ∧
      {u : Vector d | dot u u = 1 ∧ annealedLaw ν (TransientPaths u) = 1} =
        {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} ∧
      {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} =
        {u : Vector d | dot u u = 1 ∧ 0 < dot v u} ∧
      (∀ u : Vector d, dot u u = 1 → dot v u ≤ 0 →
        annealedLaw ν (TransientPaths u) = 0) := by
  obtain ⟨v, hvℓ, hv⟩ := velocity_of_positive_escape hd ν hue ℓ hℓ hpos
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, lt_self_iff_false] at hvℓ
  have hvprob : annealedLaw ν (VelocityPaths v) = 1 :=
    (mem_ae_iff_prob_eq_one (measurableSet_velocityPaths v)).mp hv
  have hunique : ∀ w : Vector d, annealedLaw ν (VelocityPaths w) = 1 → w = v := by
    intro w hw
    apply hasVelocity_unique ν _ hv
    exact (mem_ae_iff_prob_eq_one (measurableSet_velocityPaths w)).mpr hw
  have hpositive (u : Vector d) (hu : dot u u = 1) :
      0 < annealedLaw ν (TransientPaths u) ↔ 0 < dot v u := by
    constructor
    · intro hp
      obtain ⟨w, hwu, hw⟩ := velocity_of_positive_escape hd ν hue u
        (unit_direction_ne_zero u hu) hp
      have hwv : w = v := hasVelocity_unique ν hw hv
      simpa only [hwv] using hwu
    · intro hp
      rw [escape_probability_one_of_velocity ν v u hv hp]
      exact zero_lt_one
  have hone (u : Vector d) (hu : dot u u = 1) :
      annealedLaw ν (TransientPaths u) = 1 ↔ 0 < annealedLaw ν (TransientPaths u) := by
    constructor
    · intro h
      rw [h]
      exact zero_lt_one
    · intro h
      exact escape_probability_one_of_velocity ν v u hv ((hpositive u hu).mp h)
  refine ⟨v, hv0, hvℓ, hvprob, hunique, ?_, ?_, ?_⟩
  · ext u
    exact and_congr_right (hone u)
  · ext u
    exact and_congr_right (hpositive u)
  · intro u hu hnonpos
    apply le_antisymm _ bot_le
    exact le_of_not_gt (fun hp => (not_lt_of_ge hnonpos) ((hpositive u hu).mp hp))

end DirectionalTransience

end OAI
end
end

theorem solution : type_of% @OAI.DirectionalTransience.positive_probability_transience_velocity_hemisphere_oai := @OAI.DirectionalTransience.positive_probability_transience_velocity_hemisphere_oai
