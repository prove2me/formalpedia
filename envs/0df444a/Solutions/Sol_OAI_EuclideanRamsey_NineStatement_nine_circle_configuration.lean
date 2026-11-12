-- Prove2me | solution 1 for OAI.EuclideanRamsey.NineStatement.nine_circle_configuration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:07:07.088415+00:00
-- url     : https://prove2.me/submissions/76b7e3ec-3fd8-4914-be69-6bea2bd13ac2

import Mathlib
import Definitions.Def_EuclideanRamseyNine

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
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- Mathlib's newer name for `aemeasurable_pi_lambda` (with `f` implicit). -/
theorem _root_.AEMeasurable.of_eval {δ ι : Type*} [Countable ι] {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {μ : MeasureTheory.Measure δ} {f : δ → ∀ i, π i}
    (h : ∀ i, AEMeasurable (fun a => f a i) μ) : AEMeasurable f μ := aemeasurable_pi_lambda f h
/-- Mathlib d13f23b's `LipschitzOnWith.comp_absolutelyContinuousOnInterval`: a Lipschitz function of an
absolutely continuous one is absolutely continuous (Boltzmann EntropyIntegralBalance and JetSupersolutions,
oaiq-080). -/
theorem _root_.LipschitzOnWith.comp_absolutelyContinuousOnInterval {g f : ℝ → ℝ} {s : Set ℝ} {K : NNReal}
    {a b : ℝ} (hg : LipschitzOnWith K g s) (hmaps : ∀ t ∈ Set.uIcc a b, f t ∈ s)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b := by
  have h0 := hf
  unfold AbsolutelyContinuousOnInterval at h0 ⊢
  have h1 := h0.const_mul (K : ℝ)
  rw [mul_zero] at h1
  refine squeeze_zero' ?_ ?_ h1
  · exact Filter.Eventually.of_forall (fun E => Finset.sum_nonneg (fun i _ => dist_nonneg))
  · refine Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall (fun E hE => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' := hE.left i hi
    have := hg (hmaps _ hi'.left) (hmaps _ hi'.right)
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) this
    rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist, ENNReal.coe_toReal] at h2
/-- The `LipschitzWith` form of the previous lemma (JetSupersolutions, oaiq-080). -/
theorem _root_.LipschitzWith.comp_absolutelyContinuousOnInterval {g f : ℝ → ℝ} {K : NNReal}
    {a b : ℝ} (hg : LipschitzWith K g) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b :=
  (hg.lipschitzOnWith (s := Set.univ)).comp_absolutelyContinuousOnInterval (fun _ _ => Set.mem_univ _) hf
/-- Mathlib d13f23b's `Finset.equivOfEq`: the equivalence between the subtypes of equal finsets
(Coboundary CongruenceFrames, 2026-10-26). -/
def _root_.Finset.equivOfEq {α : Type*} {s t : Finset α} (h : s = t) : s ≃ t :=
  Equiv.subtypeEquivRight (fun _ => by rw [h])
/-- Mathlib d13f23b's `Finsupp.mapDomain_fintype`: on a finite index type `mapDomain f v` is the
sum of the point masses at the images (Thomason Polyhedra, oaiq-043). -/
theorem _root_.Finsupp.mapDomain_fintype {α β M : Type*} [Fintype α] [AddCommMonoid M]
    (f : α → β) (v : α →₀ M) : Finsupp.mapDomain f v = ∑ i, Finsupp.single (f i) (v i) := by
  rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp)]

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
/-- The `mpr` direction of Mathlib d13f23b's `unifIntegrable_iff`, whose `UnifIntegrable` takes
extended-real `ε` and `δ` and bounds `eLpNorm (f i) p (μ.restrict s)`; ours takes real ones and a
measurable set `s` (SLE IntegralLimits, oaiq-027). -/
theorem unifIntegrable_of_enn {α β ι : Type*} {m : MeasurableSpace α} [NormedAddCommGroup β]
    {f : ι → α → β} {p : ENNReal} {μ : MeasureTheory.Measure α}
    (h : ∀ ε : ENNReal, 0 < ε → ∃ δ : ENNReal, 0 < δ ∧
      ∀ i s, μ s ≤ δ → MeasureTheory.eLpNorm (f i) p (μ.restrict s) ≤ ε) :
    MeasureTheory.UnifIntegrable f p μ := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  have hne : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨(min δ 1).toReal, ENNReal.toReal_pos (lt_min hδ one_pos).ne' hne,
    fun i s hsm hs => ?_⟩
  rw [MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hsm]
  refine hb i s (hs.trans ?_)
  rw [ENNReal.ofReal_toReal hne]
  exact min_le_left _ _
/-- Mathlib d13f23b's `Measure.isProbabilityMeasure_of_map`, which takes the map's measurability; ours takes
the function `f`, and `_` there leaves the instance argument stuck (HardSphere, oaiq-054). -/
theorem isProbabilityMeasure_of_map_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {f : α → β} [MeasureTheory.IsProbabilityMeasure (μ.map f)]
    (_hf : AEMeasurable f μ) : MeasureTheory.IsProbabilityMeasure μ :=
  MeasureTheory.Measure.isProbabilityMeasure_of_map f
/-- Mathlib d13f23b's `FiniteMeasure.mass_map_le`, which takes the map's measurability; ours takes `f` and
`μ`, and `_ _` there leaves `f` undetermined (BalancedRyser, oaiq-063). -/
theorem finiteMeasure_mass_map_le {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {f : Ω → Ω'} {μ : MeasureTheory.FiniteMeasure Ω} (_hf : AEMeasurable f (μ : MeasureTheory.Measure Ω)) :
    (μ.map f).mass ≤ μ.mass :=
  MeasureTheory.FiniteMeasure.mass_map_le f μ
/-- Mathlib d13f23b's `lintegral_map_le f (hg : AEMeasurable g μ)`; ours is `lintegral_map_le f g` (CoulombAtom,
oaiq-071). -/
theorem lintegral_map_le_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : MeasureTheory.Measure α}
    (f : β → ENNReal) {g : α → β} (_hg : AEMeasurable g μ) :
    ∫⁻ a, f a ∂MeasureTheory.Measure.map g μ ≤ ∫⁻ a, f (g a) ∂μ :=
  MeasureTheory.lintegral_map_le f g
/-- Mathlib d13f23b's `Measure.lintegral_bind_le f m (hμ : AEMeasurable μ m)`; ours is `lintegral_bind_le f m μ`
(CoulombAtom, oaiq-071). -/
theorem lintegral_bind_le_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (f : β → ENNReal)
    (m : MeasureTheory.Measure α) {μ : α → MeasureTheory.Measure β} (_hμ : AEMeasurable μ m) :
    ∫⁻ x, f x ∂MeasureTheory.Measure.bind m μ ≤ ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m :=
  MeasureTheory.Measure.lintegral_bind_le f m μ
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- Mathlib's newer `SimpleGraph.Walk.length_le_bypass_length_iff` (ours has the two directions
separately). `_root_`, so `p.length_le_bypass_length_iff` resolves by dot notation. -/
theorem _root_.SimpleGraph.Walk.length_le_bypass_length_iff {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] {u v : V} (p : G.Walk u v) : p.length ≤ p.bypass.length ↔ p.bypass = p :=
  ⟨p.bypass_eq_self_of_length_le_length_bypass, fun h => by rw [h]⟩
/-- Mathlib d13f23b's `SimpleGraph.ncard_neighborSet`: the neighbour set's `Set.ncard` is the degree. -/
theorem _root_.SimpleGraph.ncard_neighborSet {V : Type*} (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] : (G.neighborSet v).ncard = G.degree v := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
/-- Mathlib d13f23b's `spectralRadius_eq_of_unital`: the spectral radius is the supremum of the norms over the spectrum. -/
theorem spectralRadius_eq_of_unital {𝕜 A : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A] (a : A) :
    spectralRadius 𝕜 a = ⨆ k ∈ spectrum 𝕜 a, (‖k‖₊ : ENNReal) := rfl
/-- Mathlib d13f23b's `MvPolynomial.monomial_mul_monomial`; ours is `MvPolynomial.monomial_mul`. -/
theorem _root_.MvPolynomial.monomial_mul_monomial {σ R : Type*} [CommSemiring R] {s s' : σ →₀ ℕ}
    {a b : R} : MvPolynomial.monomial s a * MvPolynomial.monomial s' b =
      MvPolynomial.monomial (s + s') (a * b) := MvPolynomial.monomial_mul
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
/-- Mathlib d13f23b's `condDistrib_ae_eq_of_measure_eq_compProd hX hY hκ`; ours takes `X` explicitly and
no `hX` (MultipleMixing Arrays, 2026-10-26). Declared in `OAI`, so a use under `open ProbabilityTheory`
is an overload and the one that typechecks wins. -/
theorem condDistrib_ae_eq_of_measure_eq_compProd
    {Ω β 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β} {m𝓨 : MeasurableSpace 𝓨}
    [StandardBorelSpace 𝓨] [Nonempty 𝓨] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {X : Ω → β} {Y : Ω → 𝓨}
    (_hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {κ : ProbabilityTheory.Kernel β 𝓨} [ProbabilityTheory.IsFiniteKernel κ]
    (hκ : μ.map (fun x => (X x, Y x)) = (μ.map X).compProd κ) :
    ProbabilityTheory.condDistrib Y X μ =ᵐ[μ.map X] κ :=
  ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd X hY hκ
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
/-- d13f23b's `NonUnitalStarRingHom.ofClass`: the bundled hom of a hom class (Kadison commutator
FreeSymmetry10, oaiq-039). `StarRing` rather than bare `Star`, so the `Star` instances agree with those of
`NonUnitalStarRingHom.map_le_map_of_map_star` (MatrixVectorTrace, `CStarMatrix`). -/
def nonUnitalStarRingHomOfClass {F R S : Type*} [NonUnitalSemiring R] [NonUnitalSemiring S]
    [StarRing R] [StarRing S] [FunLike F R S] [NonUnitalRingHomClass F R S] [StarHomClass F R S] (f : F) :
    R →⋆ₙ+* S :=
  { (f : R →ₙ+* S) with map_star' := map_star f }
/-- d13f23b's `Transcendental.ne_zero`: a transcendental element is nonzero (PiExponent CurveZeroPole,
oaiq-068). -/
theorem _root_.Transcendental.ne_zero {R A : Type*} [CommRing R] [Nontrivial R] [Ring A] [Algebra R A] {x : A}
    (h : Transcendental R x) : x ≠ 0 := fun hx => h (hx ▸ isAlgebraic_zero)
section X
variable {𝕜 𝕜₂ E Eₗ F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup Eₗ] [NormedSpace 𝕜 Eₗ] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F] [CompleteSpace F]

/-- d13f23b's `LinearMap.extendOfIsometry`: a semilinear map into a complete space that agrees in norm
with a dense-range map `e` extends along `e` to a semilinear isometry. -/
noncomputable def _root_.LinearMap.extendOfIsometry (f : E →ₛₗ[σ] F) {e : E →ₗ[𝕜] Eₗ}
    (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) : Eₗ →ₛₗᵢ[σ] F :=
  { toLinearMap := (f.extendOfNorm e).toLinearMap
    norm_map' := by
      intro x
      refine h_dense.induction_on x (isClosed_eq (by fun_prop) continuous_norm) ?_
      intro y
      have := LinearMap.extendOfNorm_eq (f := f) (e := e) h_dense ⟨1, by simp [h_norm]⟩ y
      simp only [ContinuousLinearMap.coe_coe, this, h_norm] }

omit [RingHomIsometric σ] in
theorem _root_.LinearMap.extendOfIsometry_eq (f : E →ₛₗ[σ] F) {e : E →ₗ[𝕜] Eₗ}
    (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) (x : E) :
    f.extendOfIsometry h_dense h_norm (e x) = f x :=
  LinearMap.extendOfNorm_eq (f := f) (e := e) h_dense ⟨1, by simp [h_norm]⟩ x
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
/-- d13f23b's `NonUnitalStarAlgHom.map_le_map_iff`: an injective ⋆-homomorphism of non-unital C⋆-algebras
reflects the order (Kadison similarity, oaiq-075). -/
theorem _root_.NonUnitalStarAlgHom.map_le_map_iff {F A B : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] [PartialOrder A] [StarOrderedRing A] [PartialOrder B]
    [StarOrderedRing B] [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (φ : F) (hφ : Function.Injective φ) {a b : A} : φ a ≤ φ b ↔ a ≤ b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← sub_nonneg] at h ⊢
    rw [← map_sub] at h
    generalize b - a = z at h
    have hsa : IsSelfAdjoint z := by
      apply hφ
      rw [map_star]
      exact IsSelfAdjoint.of_nonneg h
    let ψ := Unitization.starMap (φ : A →⋆ₙₐ[ℂ] B)
    have hψ : Function.Injective ψ := Unitization.starMap_injective hφ
    have hz : 0 ≤ (ψ (z : Unitization ℂ A)) := by
      rw [Unitization.starMap_inr]
      exact Unitization.inr_nonneg_iff.mpr h
    have hsa' : IsSelfAdjoint (z : Unitization ℂ A) := hsa.inr ℂ
    rw [← Unitization.inr_nonneg_iff]
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hsa'] 
    intro x hx
    have := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (hsa'.map ψ)).mp hz
    rw [hsa'.map_spectrum_real ψ hψ] at this
    exact this x hx
  · exact OrderHomClass.mono φ h
/-- d13f23b's `IsSelfAdjoint.norm_le_max_of_le_of_le`: a selfadjoint element squeezed between `a` and `b`
has norm at most `max ‖a‖ ‖b‖` (Kadison similarity, oaiq-075). -/
theorem _root_.IsSelfAdjoint.norm_le_max_of_le_of_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a b x : A} (hlo : a ≤ x) (hhi : x ≤ b) (hx : IsSelfAdjoint x) :
    ‖x‖ ≤ max ‖a‖ ‖b‖ := by
  by_cases! nontriv : Nontrivial A
  swap
  · have : x = 0 := Subsingleton.elim _ _
    simp [this]
  have hb : IsSelfAdjoint b := by
    have h1 : IsSelfAdjoint (b - x) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hhi)
    simpa using h1.add hx
  have ha : IsSelfAdjoint a := by
    have h1 : IsSelfAdjoint (x - a) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hlo)
    simpa using hx.sub h1
  have hbx : x ≤ algebraMap ℝ A ‖b‖ := hhi.trans hb.le_algebraMap_norm_self
  have hax : -(algebraMap ℝ A ‖a‖) ≤ x := ha.neg_algebraMap_norm_le_self.trans hlo
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hx with h | h
  · exact ((le_algebraMap_iff_spectrum_le hx).mp hbx _ h).trans (le_max_right _ _)
  · have hax' : algebraMap ℝ A (-‖a‖) ≤ x := by simpa using hax
    have := (algebraMap_le_cfc_iff (R := ℝ) id (-‖a‖) x).mp (by rwa [cfc_id ℝ x hx]) _ h
    simp only [id] at this
    exact (by linarith : ‖x‖ ≤ ‖a‖).trans (le_max_left _ _)
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
open scoped ComplexOrder in
/-- A norm-one functional on a C⋆-algebra with `φ 1 = 1` is monotone; stands in for d13f23b's
`ContinuousLinearMap.monotone_iff_opNorm_eq_map_one` (Kadison similarity, oaiq-075). -/
theorem monotone_of_opNorm_eq_one_of_apply_one {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Nontrivial A] (φ : A →L[ℂ] ℂ) (hn : ‖φ‖ = 1) (h1 : φ 1 = 1) :
    Monotone φ := by
  have hle : ∀ z : A, ‖φ z‖ ≤ ‖z‖ := fun z => by
    simpa [hn] using φ.le_opNorm z
  -- selfadjoint elements have real values
  have him : ∀ h : A, IsSelfAdjoint h → (φ h).im = 0 := by
    intro h hh
    by_contra hy
    set y := (φ h).im with hy_def
    set x := (φ h).re with hx_def
    set C : ℝ := x ^ 2 + y ^ 2 - ‖h‖ ^ 2 with hC
    have hD : 0 < |C| + 1 := by positivity
    set t : ℝ := -y / (|C| + 1) with ht
    set z : A := (1 : A) + ((t : ℂ) * Complex.I) • h with hz
    have hzz : star z * z = (1 : A) + ((t ^ 2 : ℝ) : ℂ) • (h * h) := by
      have hs : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
        simp [Complex.conj_ofReal]
      have ht2 : ((t ^ 2 : ℝ) : ℂ) = -(((t : ℂ) * Complex.I) * ((t : ℂ) * Complex.I)) := by
        push_cast; ring_nf; simp [Complex.I_sq]
      rw [ht2]
      simp only [hz, star_add, star_one, star_smul, hh.star_eq, hs, add_mul, mul_add, one_mul, mul_one,
        smul_mul_assoc, mul_smul_comm, smul_smul, neg_smul, smul_neg, neg_mul, smul_add]
      module
    have hnz : ‖z‖ ^ 2 ≤ 1 + t ^ 2 * ‖h‖ ^ 2 := by
      have h0 : ‖z‖ * ‖z‖ = ‖star z * z‖ := (CStarRing.norm_star_mul_self).symm
      rw [sq, h0, hzz]
      calc ‖(1 : A) + ((t ^ 2 : ℝ) : ℂ) • (h * h)‖ ≤ ‖(1 : A)‖ + ‖((t ^ 2 : ℝ) : ℂ) • (h * h)‖ := norm_add_le _ _
        _ ≤ 1 + t ^ 2 * (‖h‖ * ‖h‖) := by
          rw [norm_one, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
          gcongr
          exact norm_mul_le _ _
        _ = 1 + t ^ 2 * ‖h‖ ^ 2 := by ring
    have hphiz : φ z = (1 - t * y : ℝ) + (t * x : ℝ) * Complex.I := by
      have hh' : φ h = (x : ℂ) + (y : ℂ) * Complex.I := (Complex.re_add_im (φ h)).symm
      rw [hz, map_add, map_smul, h1, smul_eq_mul, hh']
      apply Complex.ext <;> simp <;> ring
    have hphin : ‖φ z‖ ^ 2 = (1 - t * y) ^ 2 + (t * x) ^ 2 := by
      rw [hphiz, Complex.sq_norm, Complex.normSq_apply]
      simp; ring
    have hineq : (1 - t * y) ^ 2 + (t * x) ^ 2 ≤ 1 + t ^ 2 * ‖h‖ ^ 2 := by
      rw [← hphin]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hle z) 2).trans hnz
    have hkey : y ^ 2 * (C + 2 * (|C| + 1)) ≤ 0 := by
      have e1 : t * (|C| + 1) = -y := by rw [ht]; field_simp
      have : t ^ 2 * C - 2 * t * y ≤ 0 := by rw [hC]; nlinarith [hineq]
      have h3 : (t * (|C| + 1)) ^ 2 * C - 2 * (t * (|C| + 1)) * y * (|C| + 1) ≤ 0 := by
        have := mul_nonneg (le_of_lt (pow_pos hD 2)) (neg_nonneg.mpr this)
        nlinarith [this]
      rw [e1] at h3
      nlinarith [h3]
    have hCpos : 0 < C + 2 * (|C| + 1) := by
      have := neg_abs_le C
      linarith
    have hy2 : y ^ 2 ≤ 0 := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_pos hcon hCpos]
    exact hy (by nlinarith [sq_nonneg y])
  -- nonnegative elements have nonnegative values
  have hpos : ∀ c : A, 0 ≤ c → 0 ≤ φ c := by
    intro c hc
    have hsa : IsSelfAdjoint c := IsSelfAdjoint.of_nonneg hc
    have hre := him c hsa
    set r : ℝ := ‖c‖ with hr
    have hcr : c ≤ algebraMap ℝ A r := hsa.le_algebraMap_norm_self
    have hnn : 0 ≤ algebraMap ℝ A r - c := sub_nonneg.mpr hcr
    have hle2 : algebraMap ℝ A r - c ≤ algebraMap ℝ A r := sub_le_self _ hc
    have hnorm : ‖algebraMap ℝ A r - c‖ ≤ r := by
      refine (CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hle2).trans ?_
      rw [Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one, Real.norm_eq_abs, hr]
      exact le_of_eq (abs_of_nonneg (norm_nonneg _))
    have hphi : φ (algebraMap ℝ A r - c) = (r : ℂ) - φ c := by
      rw [map_sub, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, h1]
      simp
    have hb := (hle _).trans hnorm
    rw [hphi] at hb
    have hx : φ c = ((φ c).re : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rw [hx] at hb
    have : ‖(r : ℂ) - ((φ c).re : ℂ)‖ = |r - (φ c).re| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [this] at hb
    have := (abs_le.mp hb).2
    rw [Complex.nonneg_iff]
    exact ⟨by linarith, by simp [hre]⟩
  intro a b hab
  have := hpos (b - a) (sub_nonneg.mpr hab)
  rw [map_sub] at this
  exact sub_nonneg.mp this
open scoped ComplexOrder in
/-- d13f23b's `PositiveLinearMap.norm_map_star_mul_sq_le`: Cauchy–Schwarz for a positive functional
(Kadison similarity, oaiq-075). -/
theorem _root_.PositiveLinearMap.norm_map_star_mul_sq_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →ₚ[ℂ] ℂ) (a b : A) :
    ‖ψ (star a * b)‖ ^ 2 ≤ ‖ψ (star a * a)‖ * ‖ψ (star b * b)‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (ψ.toPreGNS a) (ψ.toPreGNS b)
  rw [PositiveLinearMap.preGNS_inner_def] at h
  have ha := ψ.preGNS_norm_sq (ψ.toPreGNS a)
  have hb := ψ.preGNS_norm_sq (ψ.toPreGNS b)
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS] at h ha hb
  have h2 := mul_self_le_mul_self (norm_nonneg _) h
  rw [← ha, ← hb]
  simpa [sq, mul_mul_mul_comm] using h2
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
open scoped ComplexOrder in
/-- d13f23b's `PositiveLinearMap.norm_map_star_mul_le`: Cauchy–Schwarz for a positive functional,
with square roots (weak infiniteness, q246). -/
theorem _root_.PositiveLinearMap.norm_map_star_mul_le {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (ψ : A →ₚ[ℂ] ℂ) (a b : A) :
    ‖ψ (star a * b)‖ ≤ Real.sqrt ‖ψ (star a * a)‖ * Real.sqrt ‖ψ (star b * b)‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (ψ.toPreGNS a) (ψ.toPreGNS b)
  rw [PositiveLinearMap.preGNS_inner_def] at h
  have ha := ψ.preGNS_norm_sq (ψ.toPreGNS a)
  have hb := ψ.preGNS_norm_sq (ψ.toPreGNS b)
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS] at h ha hb
  have hna : ‖ψ.toPreGNS a‖ = Real.sqrt ‖ψ (star a * a)‖ := by
    rw [← ha, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Real.sqrt_sq (norm_nonneg _)]
  have hnb : ‖ψ.toPreGNS b‖ = Real.sqrt ‖ψ (star b * b)‖ := by
    rw [← hb, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Real.sqrt_sq (norm_nonneg _)]
  rw [← hna, ← hnb]
  exact h

/-- d13f23b's `IsUnital.toCStarAlgebra`: a non-unital C⋆-algebra with an identity is a C⋆-algebra (weak infiniteness, q246). -/
@[instance_reducible]
noncomputable def IsUnital.toCStarAlgebra {A : Type*} [NonUnitalCStarAlgebra A] [IsUnital A] :
    CStarAlgebra A :=
  letI : NormedRing A := IsUnital.toNormedRing
  letI : Algebra ℂ A := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  letI : NormedAlgebra ℂ A := { (inferInstance : Algebra ℂ A) with
    norm_smul_le := fun r x => norm_smul_le r x }
  { (inferInstance : NormedRing A), (inferInstance : NormedAlgebra ℂ A) with
    toStarRing := inferInstance
    toCompleteSpace := inferInstance
    toCStarRing := inferInstance
    toStarModule := inferInstance }
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `Complex.hasTemperateGrowth_exp_mul_I`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem hasTemperateGrowth_exp_mul_I : (fun x : ℝ => Complex.exp (x * Complex.I)).HasTemperateGrowth := by
  have hit : ∀ n : ℕ, iteratedDeriv n (fun x : ℝ => Complex.exp (Complex.I * (x:ℂ)))
      = fun x : ℝ => Complex.I ^ n * Complex.exp (Complex.I * (x:ℂ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have h1 : HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * (x:ℂ)))
          (Complex.exp (Complex.I * (x:ℂ)) * Complex.I) x := by
        have := ((hasDerivAt_id x).ofReal_comp.const_mul Complex.I).cexp
        simpa using this
      have h2 := h1.const_mul (Complex.I ^ n)
      rw [h2.deriv]
      ring
  refine ⟨?_, fun n => ⟨0, 1, fun x => ?_⟩⟩
  · exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  · have h : (fun x : ℝ => Complex.exp (x * Complex.I)) = fun x : ℝ => Complex.exp (Complex.I * (x:ℂ)) := by
      funext x; rw [mul_comm]
    rw [h, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hit]
    simp [norm_pow, Complex.norm_exp]
/-- Mathlib d13f23b's `integral_comp_log_Ioi_zero`: the substitution `y = log x` over `Ioi 0` (JointDickman
MellinSieveProfile, CubicMoment, q142). -/
theorem integral_comp_log_Ioi_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ x in Set.Ioi (0 : ℝ), x⁻¹ • g (Real.log x) = ∫ y, g y := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := (Set.univ : Set ℝ))
    (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) (fun x => x⁻¹ • g (Real.log x))
  rw [Set.image_univ, Real.range_exp] at h
  rw [h, MeasureTheory.setIntegral_univ]
  congr 1; funext x
  simp [abs_of_pos (Real.exp_pos x), smul_smul, Real.exp_ne_zero]
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
open scoped ContDiff in
/-- Backport (Mathlib d13f23b), with Mathlib's own proof: the iterated derivatives up to order `m` of a
smooth compactly supported function are uniformly bounded (Falconer all dimensions, oaiq-088: 3 modules;
OAIHecke carried its own copy). -/
theorem _root_.HasCompactSupport.exists_bound_iteratedFDeriv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} (hf : HasCompactSupport f) (hf' : ContDiff 𝕜 ∞ f) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C := by
  have key i : ∃ C, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C :=
    (hf'.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hf.iteratedFDeriv i)
  choose A hA using key
  refine ⟨max 0 ((Finset.range (m + 1)).sup' ⟨0, by simp⟩ A), le_max_left _ _, fun i hi y ↦ ?_⟩
  grw [hA i y, ← le_max_right]
  exact Finset.le_sup' A (by grind)
open scoped Matrix in
/-- Mathlib d13f23b's `Matrix.posSemidef_is_closed` (real matrices): positive semidefinite matrices are
closed (EinsteinFour JacobiCompressionLimit, oaiq-091). -/
theorem _root_.Matrix.posSemidef_is_closed {n : Type*} [Fintype n] :
    IsClosed {M : Matrix n n ℝ | M.PosSemidef} := by
  have h : {M : Matrix n n ℝ | M.PosSemidef} =
      {M : Matrix n n ℝ | M.IsHermitian} ∩
        ⋂ x : n → ℝ, {M : Matrix n n ℝ | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp [Matrix.posSemidef_iff_dotProduct_mulVec]
  rw [h]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => ?_)
  · exact isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id
  · exact isClosed_le continuous_const (by fun_prop)
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
open ProbabilityTheory MeasureTheory ENNReal in
/-- Mathlib d13f23b's `Measure.withDensity_comp`: a density on `κ ∘ₘ μ` moves into the kernel (Boltzmann
PositiveSourceFormula, q141). -/
theorem _root_.MeasureTheory.Measure.withDensity_comp {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {m𝓨 : MeasurableSpace 𝓨} {μ : Measure 𝓧} {κ : Kernel 𝓧 𝓨} [IsSFiniteKernel κ] {f' : 𝓨 → ℝ≥0∞}
    (hf' : Measurable f') :
    (κ ∘ₘ μ).withDensity f' = (κ.withDensity (fun _ b ↦ f' b)) ∘ₘ μ := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ Eq.symm ?_
  calc ∫⁻ b, g b ∂((κ.withDensity (fun _ b ↦ f' b)) ∘ₘ μ)
      = ∫⁻ a, ∫⁻ b, g b ∂(κ.withDensity (fun _ b ↦ f' b)) a ∂μ :=
        Measure.lintegral_bind (Kernel.measurable _).aemeasurable hg.aemeasurable
    _ = ∫⁻ a, ∫⁻ b, f' b * g b ∂κ a ∂μ := by
        congr with a
        exact Kernel.lintegral_withDensity _ (by fun_prop) _ hg
    _ = ∫⁻ b, f' b * g b ∂(κ ∘ₘ μ) :=
        (Measure.lintegral_bind (Kernel.measurable _).aemeasurable (hf'.mul hg).aemeasurable).symm
    _ = ∫⁻ b, g b ∂((κ ∘ₘ μ).withDensity f') :=
        (lintegral_withDensity_eq_lintegral_mul _ hf' hg).symm
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
/-- d13f23b's `BorelSpace Circle`, for `circleMeasurableSpace`. -/
theorem circleBorelSpace : @BorelSpace Circle _ circleMeasurableSpace :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)
open MeasureTheory in
/-- Mathlib d13f23b's `MeasureTheory.average_add` (CircleDomains, q146). -/
theorem _root_.MeasureTheory.average_add {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : α → E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ⨍ a, (f + g) a ∂μ = ⨍ a, f a ∂μ + ⨍ a, g a ∂μ := by
  simp only [average_eq, Pi.add_apply, integral_add hf hg, smul_add]
open MeasureTheory in
/-- Mathlib d13f23b's `MeasureTheory.average_sub` (CircleDomains, q146). -/
theorem _root_.MeasureTheory.average_sub {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : α → E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ⨍ a, (f - g) a ∂μ = ⨍ a, f a ∂μ - ⨍ a, g a ∂μ := by
  simp only [average_eq, Pi.sub_apply, integral_sub hf hg, smul_sub]
open MeasureTheory in
/-- Mathlib d13f23b's `MeasureTheory.average_const_mul` (CircleDomains, q146). -/
theorem _root_.MeasureTheory.average_const_mul {α 𝕜 : Type*} [MeasurableSpace α] (μ : Measure α)
    [RCLike 𝕜] (r : 𝕜) (f : α → 𝕜) : ⨍ a, r * f a ∂μ = r * ⨍ a, f a ∂μ :=
  integral_const_mul ..
/-- Mathlib d13f23b's `Homeomorph.locallyPathConnectedSpace` (CircleDomains, q146). -/
theorem _root_.Homeomorph.locallyPathConnectedSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [LocallyPathConnectedSpace X] (h : X ≃ₜ Y) : LocallyPathConnectedSpace Y :=
  h.symm.isOpenEmbedding.locallyPathConnectedSpace
open MeasureTheory in
/-- Mathlib d13f23b's `MeasureTheory.average_nonneg_of_ae` (CircleDomains, q146). -/
theorem _root_.MeasureTheory.average_nonneg_of_ae {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] [ClosedIciTopology E] {f : α → E} (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ⨍ a, f a ∂μ :=
  integral_nonneg_of_ae <| hf.filter_mono <| Measure.ae_smul_measure_le _
open MeasureTheory in
/-- Mathlib d13f23b's `MeasureTheory.average_nonneg` (CircleDomains, q146). -/
theorem _root_.MeasureTheory.average_nonneg {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] [ClosedIciTopology E] {f : α → E} (hf : 0 ≤ f) : 0 ≤ ⨍ a, f a ∂μ :=
  integral_nonneg hf
/-- Mathlib d13f23b's `Set.Finite.isClosed_sUnion` (CircleDomains, q146). -/
theorem _root_.Set.Finite.isClosed_sUnion {X : Type*} [TopologicalSpace X] {s : Set (Set X)}
    (hs : s.Finite) (h : ∀ t ∈ s, IsClosed t) : IsClosed (⋃₀ s) := by
  rw [Set.sUnion_eq_biUnion]; exact hs.isClosed_biUnion h
/-- Mathlib d13f23b's `Finset.frontier_biUnion_subset` (CircleDomains, q146). -/
theorem _root_.Finset.frontier_biUnion_subset {X ι : Type*} [TopologicalSpace X] (I : Finset ι)
    (s : ι → Set X) : frontier (⋃ i ∈ I, s i) ⊆ ⋃ i ∈ I, frontier (s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
    refine (frontier_union_subset _ _).trans ?_
    rintro x (hx | hx)
    · exact Or.inl hx.1
    · exact Or.inr (ih hx.2)
/-- Mathlib d13f23b's `Set.Finite.frontier_biUnion_subset` (CircleDomains, q146). -/
theorem _root_.Set.Finite.frontier_biUnion_subset {X ι : Type*} [TopologicalSpace X] {I : Set ι}
    (hI : I.Finite) (s : ι → Set X) : frontier (⋃ i ∈ I, s i) ⊆ ⋃ i ∈ I, frontier (s i) := by
  simpa only [hI.mem_toFinset] using hI.toFinset.frontier_biUnion_subset s
open MeasureTheory in
/-- Mathlib d13f23b's `MeasureTheory.Measure.prod_apply₀` (CircleDomains, q146). -/
theorem _root_.MeasureTheory.Measure.prod_apply₀ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {s : Set (α × β)} (hs : NullMeasurableSet s (μ.prod ν)) :
    μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := by
  obtain ⟨t, htm, hst⟩ := hs
  rw [measure_congr hst, Measure.prod_apply htm]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod hst] with x hx
  exact (measure_congr hx).symm
/-- Mathlib d13f23b's `AbsolutelyContinuousOnInterval.congr` (CircleDomains, q146). -/
theorem _root_.AbsolutelyContinuousOnInterval.congr {X : Type*} [PseudoMetricSpace X] {f g : ℝ → X}
    {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : Set.EqOn f g (Set.uIcc a b)) : AbsolutelyContinuousOnInterval g a b := by
  apply Filter.Tendsto.congr' _ hf
  rw [Filter.eventuallyEq_inf_principal_iff]
  filter_upwards with ⟨n, I⟩ hnI
  exact Finset.sum_congr rfl fun i hi ↦ by rw [hfg (hnI.1 i hi).1, hfg (hnI.1 i hi).2]
/-- Mathlib d13f23b's public `Set.subset_image_sdiff` (private in 0df444a; CircleDomains, q146). -/
theorem _root_.Set.subset_image_sdiff {α β : Type*} (f : α → β) (s t : Set α) :
    f '' s \ f '' t ⊆ f '' (s \ t) := by
  rw [Set.sdiff_subset_iff, ← Set.image_union, Set.union_sdiff_self]
  exact Set.image_mono Set.subset_union_right
/-- Mathlib d13f23b's `exists_contDiff_support_eq_eq_one_iff` (CircleDomains, q146). -/
theorem _root_.exists_contDiff_support_eq_eq_one_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ∞} {s t : Set E} (hs : IsOpen s)
    (ht : IsClosed t) (h : t ⊆ s) :
    ∃ f : E → ℝ, ContDiff ℝ n f ∧ Set.range f ⊆ Set.Icc 0 1 ∧ Function.support f = s ∧
      (∀ x, x ∈ t ↔ f x = 1) := by
  simpa [contMDiff_iff_contDiff] using
    exists_contMDiff_support_eq_eq_one_iff (modelWithCornersSelf ℝ E) (n := n) hs ht h
/-- d13f23b's `ContinuousLinearMap.IsInvertible.eventually_nhds`: invertible operators form an open set
(SurfaceImmersion primitives, q249). -/
theorem _root_.ContinuousLinearMap.IsInvertible.eventually_nhds {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E →L[𝕜] F} (hf : f.IsInvertible) : ∀ᶠ g in nhds f, g.IsInvertible := by
  obtain ⟨e, rfl⟩ := hf
  exact Filter.mem_of_superset (ContinuousLinearEquiv.nhds e) (by rintro _ ⟨e', rfl⟩; exact ⟨e', rfl⟩)
/-- Mathlib d13f23b's `Int.sq_emod_four`: an integer square is `0` or `1` mod 4, according to parity. -/
theorem _root_.Int.sq_emod_four (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  have h : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases h with h | h | h | h <;>
    simp [pow_two, Int.mul_emod, h] <;> omega

/-- Mathlib d13f23b's `Int.squarefree_iff_prime_sq_not_dvd`. -/
theorem _root_.Int.squarefree_iff_prime_sq_not_dvd {n : ℤ} :
    Squarefree n ↔ ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ^ 2 ∣ n) := by
  rw [← Int.squarefree_natAbs, Nat.squarefree_iff_prime_squarefree]
  refine forall_congr' fun p => imp_congr_right fun hp => not_congr ?_
  rw [pow_two, ← Nat.cast_mul, Int.natCast_dvd]

/-- Mathlib d13f23b's `Int.IsFundamentalDiscr`: a fundamental discriminant is a squarefree `D ≡ 1 [4]`, or `4 * d`
with `d` squarefree and `d ≡ 2, 3 [4]`. -/
def _root_.Int.IsFundamentalDiscr (D : ℤ) : Prop :=
  (D % 4 = 1 ∧ Squarefree D) ∨ ∃ d : ℤ, D = 4 * d ∧ Squarefree d ∧ (d % 4 = 2 ∨ d % 4 = 3)

theorem _root_.Int.isFundamentalDiscr_iff_squarefree {D : ℤ} :
    Int.IsFundamentalDiscr D ↔
      (D % 4 = 1 ∧ Squarefree D) ∨ ∃ d : ℤ, D = 4 * d ∧ Squarefree d ∧ (d % 4 = 2 ∨ d % 4 = 3) :=
  Iff.rfl

theorem _root_.Int.isFundamentalDiscr_four_mul {d : ℤ} :
    Int.IsFundamentalDiscr (4 * d) ↔ Squarefree d ∧ (d % 4 = 2 ∨ d % 4 = 3) := by
  constructor
  · rintro (⟨h, _⟩ | ⟨e, he, hs, h⟩)
    · omega
    · have : e = d := by omega
      subst this; exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩
    exact Or.inr ⟨d, rfl, hs, h⟩

theorem _root_.Int.IsFundamentalDiscr.emod_four_eq_zero_or_one {D : ℤ} (h : Int.IsFundamentalDiscr D) :
    D % 4 = 0 ∨ D % 4 = 1 := by
  rcases h with ⟨h, _⟩ | ⟨e, he, _, _⟩ <;> omega

/-- d13f23b's `logDeriv_fun_comp`, the `fun x => f (g x)` form of `logDeriv_comp` (q247 Jacobsthal). -/
theorem _root_.logDeriv_fun_comp {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
    [NormedAlgebra 𝕜 𝕜'] {f : 𝕜' → 𝕜'} {g : 𝕜 → 𝕜'} {x : 𝕜} (hf : DifferentiableAt 𝕜' f (g x))
    (hg : DifferentiableAt 𝕜 g x) : logDeriv (fun x => f (g x)) x = logDeriv f (g x) * deriv g x :=
  logDeriv_comp hf hg
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
/-- Mathlib d13f23b's `BorelSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean; InvariantIsing, q258). -/
instance _root_.Matrix.compatBorelSpace {m n α : Type*} [Countable m] [Countable n] [MeasurableSpace α]
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) :=
  inferInstanceAs <| BorelSpace (m → n → α)
/-- d13f23b's `Measurable.eval_matrix` (q258). -/
lemma _root_.Measurable.eval_matrix {m n α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {i : m} {j : n} {M : β → Matrix m n α} (hM : Measurable M) : Measurable (M · i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)
/-- d13f23b's `Measurable.of_eval_matrix` (q258). -/
lemma _root_.Measurable.of_eval_matrix {m n α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (M : β → Matrix m n α) (hM : ∀ i j, Measurable (M · i j)) : Measurable M :=
  measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => hM i j))
/-- d13f23b's `Matrix.measurable_iff` (q258). -/
protected lemma _root_.Matrix.measurable_iff {m n α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {M : β → Matrix m n α} : Measurable M ↔ ∀ i j, Measurable (M · i j) :=
  ⟨fun h _ _ => h.eval_matrix, fun h => Measurable.of_eval_matrix M h⟩
/-- d13f23b's `Matrix.measurable_apply` (q258). -/
protected lemma _root_.Matrix.measurable_apply {m n α : Type*} [MeasurableSpace α] {i : m} {j : n} :
    Measurable (fun M : Matrix m n α => M i j) := measurable_id.eval_matrix
/-- d13f23b's `Matrix.measurable_of` (q258). -/
lemma _root_.Matrix.measurable_of {m n α : Type*} [MeasurableSpace α] :
    Measurable (Matrix.of (m := m) (n := n) (α := α)) := measurable_id
/-- d13f23b's `CFC.measurable_sqrt` (Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Measurable.lean; q258). -/
lemma _root_.CFC.measurable_sqrt {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [PartialOrder A] [StarOrderedRing A]
    [NonnegSpectrumClass ℝ A] [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [CompleteSpace A] [ContinuousStar A] [OrderClosedTopology A] [MeasurableSpace A] [BorelSpace A] :
    Measurable (CFC.sqrt : A → A) := by
  have h_measurable : MeasurableSet {S : A | 0 ≤ S} :=
    (isClosed_le continuous_const continuous_id).measurableSet
  classical
  convert CFC.continuousOn_sqrt.measurable_piecewise (continuousOn_const (c := 0)) h_measurable
  ext S
  by_cases hS : 0 ≤ S
  · simp [hS]
  · simp [hS, CFC.sqrt_of_not_nonneg]
open MeasureTheory ProbabilityTheory in
/-- Mathlib d13f23b's `ProbabilityTheory.rnDeriv_measure_compProd_right`: `∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)` is the kernel's
Radon-Nikodym derivative (InvariantIsing KernelRelativeEntropy, q251). -/
theorem _root_.ProbabilityTheory.rnDeriv_measure_compProd_right {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (κ η : ProbabilityTheory.Kernel α β) [ProbabilityTheory.IsFiniteKernel κ]
    [ProbabilityTheory.IsFiniteKernel η] :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p => κ.rnDeriv η p.1 p.2 := by
  have h : κ = η.withDensity (κ.rnDeriv η) + κ.singularPart η :=
    (Kernel.rnDeriv_add_singularPart κ η).symm
  have hf : Measurable (Function.uncurry (κ.rnDeriv η)) := Kernel.measurable_rnDeriv κ η
  have hsum : μ ⊗ₘ κ = μ ⊗ₘ κ.singularPart η + (μ ⊗ₘ η).withDensity (fun p => κ.rnDeriv η p.1 p.2) := by
    conv_lhs => rw [h]
    rw [Measure.compProd_add_right, Measure.compProd_withDensity hf, add_comm]
  refine Measure.eq_rnDeriv₀ hf.aemeasurable ?_ hsum |>.symm
  exact Measure.MutuallySingular.compProd_of_right μ μ (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
/-- d13f23b's `ProbabilityTheory.charFun_map_eq_charFun_map_inner_one` (InvariantIsing CavityPrecisionTiltLaw, q251). -/
theorem _root_.ProbabilityTheory.charFun_map_eq_charFun_map_inner_one {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : MeasureTheory.Measure Ω} {Y : Ω → E} (hY : AEMeasurable Y μ) (t : E) :
    MeasureTheory.charFun (μ.map Y) t = MeasureTheory.charFun (μ.map fun ω => inner ℝ (Y ω) t) 1 := by
  have h2 : AEMeasurable (fun ω => inner ℝ (Y ω) t) μ := by fun_prop
  rw [MeasureTheory.charFun_apply, MeasureTheory.charFun_apply_real,
    MeasureTheory.integral_map hY (by fun_prop), MeasureTheory.integral_map h2 (by fun_prop)]
  simp
/-- d13f23b's `HasLaw.memLp_comp` (InvariantIsing CavityGaussianRows, q251). -/
theorem _root_.ProbabilityTheory.HasLaw.memLp_comp {Ω 𝓧 E : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure 𝓧} {X : Ω → 𝓧} {f : 𝓧 → E}
    {p : ENNReal} (hX : ProbabilityTheory.HasLaw X μ P) (hf : MeasureTheory.MemLp f p μ) :
    MeasureTheory.MemLp (f ∘ X) p P := by
  have h : MeasureTheory.MemLp f p (P.map X) := hX.map_eq ▸ hf
  exact (MeasureTheory.memLp_map_measure_iff h.aestronglyMeasurable hX.aemeasurable).1 h
/-- d13f23b's `HasLaw.memLp`: a variable whose law has `id` in `L^p` is in `L^p`. -/
theorem _root_.ProbabilityTheory.HasLaw.memLp {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}
    [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure E} {X : Ω → E}
    {p : ENNReal} (hX : ProbabilityTheory.HasLaw X μ P) (hμ : MeasureTheory.MemLp id p μ) :
    MeasureTheory.MemLp X p P := hX.memLp_comp hμ
/-- d13f23b's `HasLaw.integrable_comp` (InvariantIsing CavityGaussianRows, q251). -/
theorem _root_.ProbabilityTheory.HasLaw.integrable_comp {Ω 𝓧 E : Type*} {mΩ : MeasurableSpace Ω}
    {m𝓧 : MeasurableSpace 𝓧} [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω}
    {μ : MeasureTheory.Measure 𝓧} {X : Ω → 𝓧} {f : 𝓧 → E} (hX : ProbabilityTheory.HasLaw X μ P)
    (hf : MeasureTheory.Integrable f μ) : MeasureTheory.Integrable (f ∘ X) P := by
  have h : MeasureTheory.Integrable f (P.map X) := hX.map_eq ▸ hf
  exact (MeasureTheory.integrable_map_measure h.aestronglyMeasurable hX.aemeasurable).1 h
end OAICompat434

end OAI

universe u uIndex uDomain uCodomain uPoint

section
section
namespace OAI

noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey




def coordinateField {s d : ℕ} (a : Fin s → Space d) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ (Set.range (fun ij : Fin s × Fin d => a ij.1 ij.2))

abbrev Coeff {s d : ℕ} (a : Fin s → Space d) := ↥(coordinateField a)
abbrev TensorRing {s d : ℕ} (a : Fin s → Space d) := Coeff a ⊗[ℚ] Coeff a

def coordinate {s d : ℕ} (a : Fin s → Space d) (i : Fin s) (j : Fin d) : Coeff a :=
  ⟨a i j, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self (i, j))⟩

def augmented {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : Option (Fin d) → Coeff a
  | none => 1
  | some j => coordinate a i j

def multiply {s d : ℕ} (a : Fin s → Space d) : TensorRing a →ₐ[ℚ] Coeff a :=
  Algebra.TensorProduct.lmul' ℚ

def FieldCriterion {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∃ P : Matrix (Option (Fin d)) (Option (Fin d)) (TensorRing a),
    (∀ i : Fin s, ∑ α, ∑ β,
      ((augmented a i α) ⊗ₜ[ℚ] (1 : Coeff a)) * P α β *
      ((1 : Coeff a) ⊗ₜ[ℚ] (augmented a i β)) = 0) ∧
    (∀ α β : Fin d, multiply a (P (some α) (some β)) = if α = β then 1 else 0)

end EuclideanRamsey

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Three points on a real circle cannot occupy three distinct parameters
on a secant. No positive-radius assumption is needed. -/
theorem circle_parameter_eq_zero_or_one
    (x₀ x₁ y₀ y₁ c₀ c₁ R t : ℝ)
    (hx : (x₀-c₀)^2 + (x₁-c₁)^2 = R)
    (hy : (y₀-c₀)^2 + (y₁-c₁)^2 = R)
    (hz : (x₀+t*(y₀-x₀)-c₀)^2 + (x₁+t*(y₁-x₁)-c₁)^2 = R)
    (hxy : x₀ ≠ y₀ ∨ x₁ ≠ y₁) : t = 0 ∨ t = 1 := by
  have hnorm : (y₀-x₀)^2 + (y₁-x₁)^2 ≠ 0 := by
    intro h
    have h₀ : y₀-x₀ = 0 := by nlinarith [sq_nonneg (y₁-x₁)]
    have h₁ : y₁-x₁ = 0 := by nlinarith [sq_nonneg (y₀-x₀)]
    rcases hxy with hxy | hxy <;> apply hxy <;> linarith
  have hprod : t * (t-1) * ((y₀-x₀)^2 + (y₁-x₁)^2) = 0 := by
    linear_combination hz - (1-t)*hx - t*hy
  rcases mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hnorm) with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The determinant of a secant line is nonzero at a third distinct
point on the same circle. Distinctness excludes radius zero. -/
theorem secant_nonzero
    (x₀ x₁ y₀ y₁ z₀ z₁ c₀ c₁ R : ℝ)
    (hx : (x₀-c₀)^2 + (x₁-c₁)^2 = R)
    (hy : (y₀-c₀)^2 + (y₁-c₁)^2 = R)
    (hz : (z₀-c₀)^2 + (z₁-c₁)^2 = R)
    (hxy : x₀ ≠ y₀ ∨ x₁ ≠ y₁)
    (hxz : x₀ ≠ z₀ ∨ x₁ ≠ z₁)
    (hyz : y₀ ≠ z₀ ∨ y₁ ≠ z₁) :
    (y₀-x₀)*(z₁-x₁) - (y₁-x₁)*(z₀-x₀) ≠ 0 := by
  intro hdet
  by_cases hdx : y₀-x₀ = 0
  · have hdy : y₁-x₁ ≠ 0 := by
      intro hdy
      rcases hxy with hxy | hxy <;> apply hxy <;> linarith
    have hzx : z₀ = x₀ := by
      have : (y₁-x₁)*(z₀-x₀) = 0 := by rw [hdx] at hdet; nlinarith
      have := (mul_eq_zero.mp this).resolve_left hdy
      linarith
    let t := (z₁-x₁)/(y₁-x₁)
    have ht : x₁+t*(y₁-x₁) = z₁ := by dsimp [t]; field_simp <;> ring
    have htx : x₀+t*(y₀-x₀) = z₀ := by rw [hdx]; simp [hzx]
    have he := circle_parameter_eq_zero_or_one x₀ x₁ y₀ y₁ c₀ c₁ R t hx hy
      (by rw [ht, htx]; exact hz) hxy
    rcases he with he | he
    · rcases hxz with h | h <;> apply h <;> simp_all
    · rcases hyz with h | h
      · apply h
        calc
          y₀ = x₀ := sub_eq_zero.mp hdx
          _ = z₀ := hzx.symm
      · apply h
        simpa [he] using ht
  · let t := (z₀-x₀)/(y₀-x₀)
    have ht : x₀+t*(y₀-x₀) = z₀ := by dsimp [t]; field_simp <;> ring
    have hty : x₁+t*(y₁-x₁) = z₁ := by
      dsimp [t]
      apply (mul_right_cancel₀ hdx)
      field_simp
      nlinarith [hdet]
    have he := circle_parameter_eq_zero_or_one x₀ x₁ y₀ y₁ c₀ c₁ R t hx hy
      (by rw [ht, hty]; exact hz) hxy
    rcases he with he | he
    · rcases hxz with h | h <;> apply h <;> simp_all
    · rcases hyz with h | h <;> apply h <;> simp_all

/-- Restriction of a Ramsey configuration preserves its distances. -/
theorem ramsey_restrict {s t d : ℕ} (a : Fin t → Space d)
    (f : Fin s → Fin t) (ha : Ramsey a) : Ramsey (a ∘ f) := by
  intro r hr
  obtain ⟨D, hD, h⟩ := ha r hr
  refine ⟨D, hD, ?_⟩
  intro c
  obtain ⟨b, hb, k, hk⟩ := h c
  exact ⟨b ∘ f, fun i j => hb (f i) (f j), k, fun i => hk (f i)⟩

/-- A circle of zero radius is a singleton; repeated labels are allowed. -/
theorem zero_radius_ramsey {s : ℕ} (a : Fin s → Space 2)
    (c : Space 2) (h : ∀ i, dist (a i) c = 0) : Ramsey a := by
  intro r hr
  refine ⟨1, by omega, ?_⟩
  intro coloring
  refine ⟨fun _ => 0, ?_, coloring 0, fun _ => rfl⟩
  intro i j
  have hi : a i = c := dist_eq_zero.mp (h i)
  have hj : a j = c := dist_eq_zero.mp (h j)
  simp [hi, hj]

/-- The metric circle equation implies the scalar coordinate equation. -/
theorem circle_coordinates {s : ℕ} (a : Fin s → Space 2)
    (c : Space 2) (r : ℝ) (hc : ∀ i, dist (a i) c = r) :
    ∀ i, (a i 0-c 0)^2 + (a i 1-c 1)^2 = r^2 := by
  intro i
  have h := congrArg (fun x : ℝ => x^2) (hc i)
  simpa [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs] using h

end EuclideanRamsey.CircleConsequence

end

end OAI
end
end

section
section
namespace OAI
noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Rational parametrization of a genuine radius-r circle. -/
def stereographic (c : Space 2) (r t : ℝ) : Space 2 :=
  c + r • WithLp.toLp 2 ![(1-t^2)/(1+t^2), (2*t)/(1+t^2)]

theorem stereographic_recover (t : ℝ) :
    ((2*t)/(1+t^2)) / (1 + (1-t^2)/(1+t^2)) = t := by
  have hd : 1+t^2 ≠ 0 := by positivity
  have he : 1 + (1-t^2)/(1+t^2) = 2/(1+t^2) := by field_simp <;> ring
  rw [he, div_div]
  field_simp

theorem stereographic_injective (c : Space 2) (r : ℝ) (hr : 0 < r) :
    Function.Injective (stereographic c r) := by
  intro t u h
  have h₀ := congrArg (fun p : Space 2 => p 0) h
  have h₁ := congrArg (fun p : Space 2 => p 1) h
  have hx : (1-t^2)/(1+t^2) = (1-u^2)/(1+u^2) := by
    apply mul_left_cancel₀ (ne_of_gt hr)
    apply add_left_cancel (a := c 0)
    simpa only [stereographic, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply,
      Matrix.cons_val_zero, smul_eq_mul] using h₀
  have hy : (2*t)/(1+t^2) = (2*u)/(1+u^2) := by
    apply mul_left_cancel₀ (ne_of_gt hr)
    apply add_left_cancel (a := c 1)
    simpa only [stereographic, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul] using h₁
  calc
    t = ((2*t)/(1+t^2)) / (1 + (1-t^2)/(1+t^2)) := (stereographic_recover t).symm
    _ = ((2*u)/(1+u^2)) / (1 + (1-u^2)/(1+u^2)) := by rw [hx, hy]
    _ = u := stereographic_recover u

theorem stereographic_on_circle (c : Space 2) (r t : ℝ) (hr : 0 < r) :
    dist (stereographic c r t) c = r := by
  have hd : 1+t^2 ≠ 0 := by positivity
  have hs : ((1-t^2)/(1+t^2))^2 + ((2*t)/(1+t^2))^2 = 1 := by
    field_simp
    ring
  have he : dist (stereographic c r t) c ^ 2 = r^2 := by
    simp only [dist_eq_norm, stereographic, add_sub_cancel_left]
    rw [norm_smul, mul_pow]
    simp only [Real.norm_eq_abs, sq_abs, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs]
    rw [hs, mul_one]
  have hn : 0 ≤ dist (stereographic c r t) c := dist_nonneg
  nlinarith

theorem circle_infinite (c : Space 2) (r : ℝ) (hr : 0 < r) :
    {p : Space 2 | dist p c = r}.Infinite := by
  apply (Set.infinite_range_of_injective (stereographic_injective c r hr)).mono
  rintro p ⟨t, rfl⟩
  exact stereographic_on_circle c r t hr

/-- Extension adds actual distinct points on the same metric circle. -/
theorem extend_to_five {s : ℕ} (a : Fin s → Space 2)
    (hs : s ≤ 5) (ha : Function.Injective a)
    (c : Space 2) (r : ℝ) (hr : 0 < r)
    (hc : ∀ i, dist (a i) c = r) :
    ∃ b : Fin 5 → Space 2, Function.Injective b ∧
      (∀ j, dist (b j) c = r) ∧ ∃ f : Fin s → Fin 5, ∀ i, b (f i) = a i := by
  classical
  let S : Finset (Space 2) := Finset.univ.image a
  have hS : S.card = s := by simp [S, Finset.card_image_of_injective _ ha]
  have hSc : ∀ p ∈ S, dist p c = r := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hc i
  obtain ⟨T, hTc, hT⟩ := (circle_infinite c r hr).exists_subset_card_eq 5
  have hST : 5 ≤ (S ∪ T).card := by
    rw [← hT]
    exact Finset.card_le_card Finset.subset_union_right
  obtain ⟨U, hSU, hUst, hU⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left : S ⊆ S ∪ T) (by omega : S.card ≤ 5) hST
  let e : U ≃ Fin 5 := Finset.equivFinOfCardEq hU
  let b : Fin 5 → Space 2 := fun j => (e.symm j).val
  refine ⟨b, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro j
    have hj : b j ∈ S ∪ T := hUst (e.symm j).property
    rcases Finset.mem_union.mp hj with hj | hj
    · exact hSc _ hj
    · exact hTc hj
  · let f : Fin s → Fin 5 := fun i => e ⟨a i, hSU (by simp [S])⟩
    refine ⟨f, ?_⟩
    intro i
    simp [b, f]
end EuclideanRamsey.CircleConsequence

end

end OAI
end
end

section
section
namespace OAI

/- The secant equations and quadratic isolators have coefficients in the coordinate field. -/
noncomputable section
namespace EuclideanRamsey.CircleConsequence

def secantRow {s : ℕ} (a : Fin s → Space 2) (i j : Fin s) :
    Option (Fin 2) → Coeff a
  | none => coordinate a i 0 * coordinate a j 1 - coordinate a j 0 * coordinate a i 1
  | some k => if k = 0 then coordinate a i 1 - coordinate a j 1
      else coordinate a j 0 - coordinate a i 0

def secantValue {s : ℕ} (a : Fin s → Space 2) (i j k : Fin s) : Coeff a :=
  (coordinate a j 0-coordinate a i 0)*(coordinate a k 1-coordinate a i 1) -
  (coordinate a j 1-coordinate a i 1)*(coordinate a k 0-coordinate a i 0)

theorem secantRow_eval {s : ℕ} (a : Fin s → Space 2) (i j k : Fin s) :
    (∑ α : Option (Fin 2), secantRow a i j α * augmented a k α) =
      secantValue a i j k := by
  simp [secantRow, secantValue, augmented, Fin.sum_univ_two]
  ring

def pairedSecantMatrix {s : ℕ} (a : Fin s → Space 2)
    (i j k l : Fin s) : Matrix (Option (Fin 2)) (Option (Fin 2)) (Coeff a) :=
  fun α β => secantRow a i j α * secantRow a k l β

theorem pairedSecantMatrix_eval {s : ℕ} (a : Fin s → Space 2)
    (i j k l m : Fin s) :
    (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
      pairedSecantMatrix a i j k l α β * augmented a m α * augmented a m β) =
      secantValue a i j m * secantValue a k l m := by
  rw [← secantRow_eval a i j m, ← secantRow_eval a k l m]
  rw [Finset.sum_mul]
  simp only [pairedSecantMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  ring

theorem pairedSecantMatrix_vanishes {s : ℕ} (a : Fin s → Space 2)
    (i j k l m : Fin s) (hm : m = i ∨ m = j ∨ m = k ∨ m = l) :
    (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
      pairedSecantMatrix a i j k l α β * augmented a m α * augmented a m β) = 0 := by
  rw [pairedSecantMatrix_eval]
  rcases hm with rfl | rfl | rfl | rfl <;> dsimp only [secantValue] <;> ring

/-- Nonzero evaluation follows from actual planar circle equations. -/
theorem secantValue_ne_zero {s : ℕ} (a : Fin s → Space 2)
    (ha : Function.Injective a) (c : Space 2) (R : ℝ)
    (hc : ∀ m, (a m 0-c 0)^2 + (a m 1-c 1)^2 = R)
    (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    secantValue a i j k ≠ 0 := by
  have different (u v : Fin s) (huv : u ≠ v) :
      a u 0 ≠ a v 0 ∨ a u 1 ≠ a v 1 := by
    by_contra h
    push Not at h
    apply huv
    apply ha
    ext q
    fin_cases q <;> simp_all
  have h := secant_nonzero (a i 0) (a i 1) (a j 0) (a j 1)
    (a k 0) (a k 1) (c 0) (c 1) R (hc i) (hc j) (hc k)
    (different i j hij) (different i k hik) (different j k hjk)
  intro hz
  apply h
  have he := congrArg (fun z : Coeff a => (z : ℝ)) hz
  simpa [secantValue, coordinate] using he

/-- The five-point isolator is a concrete coordinate-field matrix.
The permutation is just a labeling, with e 0 the point being isolated. -/
theorem five_point_isolator (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (R : ℝ)
    (hc : ∀ m, (a m 0-c 0)^2 + (a m 1-c 1)^2 = R)
    (e : Equiv.Perm (Fin 5)) :
    ∃ M : Matrix (Option (Fin 2)) (Option (Fin 2)) (Coeff a),
      (∀ m, m ≠ e 0 →
        (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
          M α β * augmented a m α * augmented a m β) = 0) ∧
      (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
          M α β * augmented a (e 0) α * augmented a (e 0) β) ≠ 0 := by
  refine ⟨pairedSecantMatrix a (e 1) (e 2) (e 3) (e 4), ?_, ?_⟩
  · intro m hm
    apply pairedSecantMatrix_vanishes
    have hem : e (e.symm m) = m := e.apply_symm_apply m
    have hn : e.symm m ≠ 0 := by intro h; apply hm; simpa [h] using hem.symm
    generalize h : e.symm m = k at hem hn
    fin_cases k <;> simp_all
  · rw [pairedSecantMatrix_eval]
    apply mul_ne_zero
    · apply secantValue_ne_zero a ha c R hc <;> exact e.injective.ne (by decide)
    · apply secantValue_ne_zero a ha c R hc <;> exact e.injective.ne (by decide)

end EuclideanRamsey.CircleConsequence

end

end OAI
end
end

section
section
namespace OAI
noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Three actual distinct circle points already affinely span the plane.
The inverse two-by-two determinant is written explicitly. -/
theorem circle_five_affineSpan (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (r : ℝ)
    (hc : ∀ i, dist (a i) c = r) : affineSpan ℝ (Set.range a) = ⊤ := by
  classical
  let A := affineSpan ℝ (Set.range a)
  have hp (i : Fin 5) : a i ∈ A := mem_affineSpan ℝ (Set.mem_range_self i)
  let u := a 1 - a 0
  let v := a 2 - a 0
  let D : ℝ := u 0 * v 1 - v 0 * u 1
  have hfield := secantValue_ne_zero a ha c (r^2) (circle_coordinates a c r hc)
    0 1 2 (by decide) (by decide) (by decide)
  have hD : D ≠ 0 := by
    intro h
    apply hfield
    apply Subtype.ext
    simpa [D, u, v, secantValue, coordinate, mul_comm] using h
  have hu : u ∈ A.direction := by
    simpa [u, vsub_eq_sub] using AffineSubspace.vsub_mem_direction (hp 1) (hp 0)
  have hv : v ∈ A.direction := by
    simpa [v, vsub_eq_sub] using AffineSubspace.vsub_mem_direction (hp 2) (hp 0)
  apply top_unique
  intro x hx
  let w := x - a 0
  let α : ℝ := (w 0 * v 1 - v 0 * w 1) / D
  let β : ℝ := (u 0 * w 1 - w 0 * u 1) / D
  have hcomb : α • u + β • v = w := by
    ext j
    fin_cases j <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
      dsimp [α, β] <;>
      field_simp [hD] <;>
      dsimp [D] <;> ring
  have hm : α • u + β • v ∈ A.direction :=
    A.direction.add_mem (A.direction.smul_mem α hu) (A.direction.smul_mem β hv)
  have he := AffineSubspace.vadd_mem_of_mem_direction hm (hp 0)
  simpa [hcomb, w, vadd_eq_add] using he
end EuclideanRamsey.CircleConsequence

end

end OAI
end
end

section
section
namespace OAI

/-! Rational parametrization of the unit circle and its coordinate field. -/

noncomputable section
namespace EuclideanRamsey.NineGeometry

def circlePoint (x : ℝ) : Space 2 :=
  CircleConsequence.stereographic (0 : Space 2) 1 x

def circleConfig (t : Fin 9 → ℝ) (i : Fin 9) : Space 2 := circlePoint (t i)

@[simp] theorem circlePoint_zero (x : ℝ) :
    circlePoint x 0 = (1 - x^2) / (1 + x^2) := by
  simp [circlePoint, CircleConsequence.stereographic]

@[simp] theorem circlePoint_one (x : ℝ) :
    circlePoint x 1 = (2*x) / (1 + x^2) := by
  simp [circlePoint, CircleConsequence.stereographic]

theorem circlePoint_recover (x : ℝ) :
    circlePoint x 1 / (1 + circlePoint x 0) = x := by
  simpa only [circlePoint_zero, circlePoint_one] using
    CircleConsequence.stereographic_recover x

theorem circlePoint_on_circle (x : ℝ) : dist (circlePoint x) 0 = 1 :=
  CircleConsequence.stereographic_on_circle 0 1 x (by norm_num)

theorem circlePoint_injective : Function.Injective circlePoint := by
  intro x y h
  have hr := congrArg (fun p : Space 2 => p 1 / (1 + p 0)) h
  simpa only [circlePoint_recover] using hr

theorem circleConfig_on_circle (t : Fin 9 → ℝ) (i : Fin 9) :
    dist (circleConfig t i) 0 = 1 := circlePoint_on_circle (t i)

theorem circleConfig_injective (t : Fin 9 → ℝ)
    (ht : AlgebraicIndependent ℚ t) : Function.Injective (circleConfig t) :=
  circlePoint_injective.comp ht.injective

/-- Restriction to the first five points. -/
def firstFive (i : Fin 5) : Fin 9 := ⟨i.val, by omega⟩

theorem firstFive_injective : Function.Injective firstFive := by
  intro i j h
  apply Fin.ext
  simpa only [firstFive] using congrArg (fun k : Fin 9 => k.val) h

theorem circleConfig_affineSpan (t : Fin 9 → ℝ)
    (ht : AlgebraicIndependent ℚ t) :
    affineSpan ℝ (Set.range (circleConfig t)) = ⊤ := by
  have hfive : affineSpan ℝ (Set.range (circleConfig t ∘ firstFive)) = ⊤ :=
    CircleConsequence.circle_five_affineSpan (circleConfig t ∘ firstFive)
      ((circleConfig_injective t ht).comp firstFive_injective) 0 1
      (fun i => circleConfig_on_circle t (firstFive i))
  apply top_unique
  rw [← hfive]
  apply affineSpan_mono
  rintro p ⟨i, rfl⟩
  exact Set.mem_range_self (firstFive i)

/-- The coordinate field is generated by the circle parameters. -/
theorem circleConfig_coordinateField (t : Fin 9 → ℝ) :
    coordinateField (circleConfig t) = IntermediateField.adjoin ℚ (Set.range t) := by
  let F : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ (Set.range t)
  apply le_antisymm
  · change IntermediateField.adjoin ℚ
      (Set.range (fun ij : Fin 9 × Fin 2 => circleConfig t ij.1 ij.2)) ≤ F
    apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨⟨i, j⟩, rfl⟩
    have ht : t i ∈ F := IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)
    have ht2 : (t i)^2 ∈ F := F.pow_mem ht 2
    have hden : 1 + (t i)^2 ∈ F := F.add_mem F.one_mem ht2
    fin_cases j
    · change circlePoint (t i) 0 ∈ F
      rw [circlePoint_zero]
      exact F.div_mem (F.sub_mem F.one_mem ht2) hden
    · change circlePoint (t i) 1 ∈ F
      rw [circlePoint_one]
      exact F.div_mem (F.mul_mem (F.natCast_mem 2) ht) hden
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨i, rfl⟩
    let K : IntermediateField ℚ ℝ := coordinateField (circleConfig t)
    have hcoord (j : Fin 2) : circleConfig t i j ∈ K :=
      IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self (i, j))
    have hrecovered : circleConfig t i 1 / (1 + circleConfig t i 0) ∈ K :=
      K.div_mem (hcoord 1) (K.add_mem K.one_mem (hcoord 0))
    change t i ∈ K
    simpa only [circleConfig, circlePoint_recover] using hrecovered

end EuclideanRamsey.NineGeometry

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open scoped TensorProduct

namespace EuclideanRamsey.IndependentTensor

variable (ι : Type u)

abbrev Poly := MvPolynomial ι ℚ
abbrev Rat := FractionRing (Poly ι)
abbrev JointPoly := MvPolynomial (ι ⊕ ι) ℚ
abbrev JointField := FractionRing (JointPoly ι)

/-- Mathlib drift: OpenAI's environment found `OreLocalization.instAlgebra` for `Algebra ℚ` on these fraction fields (NineField pins it by name); ours finds `DivisionRing.toRatAlgebra`, whose module is not reducibly the Ore one, so the tensor-product instances failed. -/
instance (priority := high) ratAlgebraCompat : Algebra ℚ (Rat ι) :=
  OreLocalization.instAlgebra (R₀ := ℚ) (R := Poly ι) (S := nonZeroDivisors (Poly ι))

instance (priority := high) jointFieldAlgebraCompat : Algebra ℚ (JointField ι) :=
  OreLocalization.instAlgebra (R₀ := ℚ) (R := JointPoly ι) (S := nonZeroDivisors (JointPoly ι))

def polyToRat : Poly ι →ₐ[ℚ] Rat ι :=
  IsScalarTower.toAlgHom ℚ (Poly ι) (Rat ι)

def jointToField : JointPoly ι →ₐ[ℚ] JointField ι :=
  IsScalarTower.toAlgHom ℚ (JointPoly ι) (JointField ι)

def leftPolynomialMap : Poly ι →ₐ[ℚ] JointField ι :=
  (jointToField ι).comp (MvPolynomial.rename Sum.inl)

def rightPolynomialMap : Poly ι →ₐ[ℚ] JointField ι :=
  (jointToField ι).comp (MvPolynomial.rename Sum.inr)

theorem leftPolynomialMap_injective :
    Function.Injective (leftPolynomialMap ι) :=
  (IsFractionRing.injective (JointPoly ι) (JointField ι)).comp
    (MvPolynomial.rename_injective Sum.inl Sum.inl_injective)

theorem rightPolynomialMap_injective :
    Function.Injective (rightPolynomialMap ι) :=
  (IsFractionRing.injective (JointPoly ι) (JointField ι)).comp
    (MvPolynomial.rename_injective Sum.inr Sum.inr_injective)

/-- The first rational-function copy, in the independent left variables. -/
def leftMap : Rat ι →ₐ[ℚ] JointField ι :=
  IsFractionRing.liftAlgHom (K := Rat ι) (leftPolynomialMap_injective ι)

/-- The second rational-function copy, in the independent right variables. -/
def rightMap : Rat ι →ₐ[ℚ] JointField ι :=
  IsFractionRing.liftAlgHom (K := Rat ι) (rightPolynomialMap_injective ι)

@[simp] theorem leftMap_algebraMap (p : Poly ι) :
    leftMap ι (algebraMap (Poly ι) (Rat ι) p) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.rename Sum.inl p) := by
  exact IsFractionRing.lift_algebraMap (K := Rat ι)
    (g := (leftPolynomialMap ι).toRingHom) (leftPolynomialMap_injective ι) p

@[simp] theorem rightMap_algebraMap (p : Poly ι) :
    rightMap ι (algebraMap (Poly ι) (Rat ι) p) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.rename Sum.inr p) := by
  exact IsFractionRing.lift_algebraMap (K := Rat ι)
    (g := (rightPolynomialMap ι).toRingHom) (rightPolynomialMap_injective ι) p

@[simp] theorem leftMap_X (i : ι) :
    leftMap ι (algebraMap (Poly ι) (Rat ι) (MvPolynomial.X i)) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.X (Sum.inl i)) := by
  simp

@[simp] theorem rightMap_X (i : ι) :
    rightMap ι (algebraMap (Poly ι) (Rat ι) (MvPolynomial.X i)) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.X (Sum.inr i)) := by
  simp

/-- The map to the joint rational-function field. -/
def tensorEmbedding : Rat ι ⊗[ℚ] Rat ι →ₐ[ℚ] JointField ι :=
  Algebra.TensorProduct.lift (leftMap ι) (rightMap ι) (fun _ _ => Commute.all _ _)

@[simp] theorem tensorEmbedding_tmul (x y : Rat ι) :
    tensorEmbedding ι (x ⊗ₜ[ℚ] y) = leftMap ι x * rightMap ι y := by
  rfl

@[simp] theorem tensorEmbedding_X_tmul_one (i : ι) :
    tensorEmbedding ι
      ((algebraMap (Poly ι) (Rat ι) (MvPolynomial.X i)) ⊗ₜ[ℚ] 1) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.X (Sum.inl i)) := by
  simp

@[simp] theorem tensorEmbedding_one_tmul_X (i : ι) :
    tensorEmbedding ι
      (1 ⊗ₜ[ℚ] (algebraMap (Poly ι) (Rat ι) (MvPolynomial.X i))) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.X (Sum.inr i)) := by
  simp

def localizeLeft : Poly ι ⊗[ℚ] Poly ι →ₐ[ℚ] Rat ι ⊗[ℚ] Poly ι :=
  Algebra.TensorProduct.map (polyToRat ι) (AlgHom.id ℚ (Poly ι))

def localizeRight : Rat ι ⊗[ℚ] Poly ι →ₐ[ℚ] Rat ι ⊗[ℚ] Rat ι :=
  Algebra.TensorProduct.map (AlgHom.id ℚ (Rat ι)) (polyToRat ι)

def halfEmbedding : Rat ι ⊗[ℚ] Poly ι →ₐ[ℚ] JointField ι :=
  (tensorEmbedding ι).comp (localizeRight ι)

def polynomialEmbedding : Poly ι ⊗[ℚ] Poly ι →ₐ[ℚ] JointField ι :=
  (jointToField ι).comp (MvPolynomial.tensorEquivSum ℚ ι ι ℚ).toAlgHom

theorem polynomialEmbedding_injective :
    Function.Injective (polynomialEmbedding ι) :=
  (IsFractionRing.injective (JointPoly ι) (JointField ι)).comp
    (MvPolynomial.tensorEquivSum ℚ ι ι ℚ).injective

/-- On polynomials the joint map is the standard polynomial tensor equivalence,
followed by the injective fraction-ring inclusion. -/
theorem halfEmbedding_comp_localizeLeft :
    (halfEmbedding ι).comp (localizeLeft ι) = polynomialEmbedding ι := by
  apply Algebra.TensorProduct.ext
  · ext i
    simp [halfEmbedding, localizeLeft, localizeRight, polyToRat,
      polynomialEmbedding, jointToField, IsScalarTower.toAlgHom_apply]
  · ext i
    simp [halfEmbedding, localizeLeft, localizeRight, polyToRat,
      polynomialEmbedding, jointToField, IsScalarTower.toAlgHom_apply]

/-- First localization: invert all nonzero polynomials in the left factor.
The target map detects zero on the polynomial base, hence on its localization. -/
theorem halfEmbedding_injective : Function.Injective (halfEmbedding ι) := by
  let : Algebra (Poly ι ⊗[ℚ] Poly ι) (Rat ι ⊗[ℚ] Poly ι) :=
    (localizeLeft ι).toAlgebra
  let : IsScalarTower (Poly ι) (Poly ι ⊗[ℚ] Poly ι) (Rat ι ⊗[ℚ] Poly ι) :=
    IsScalarTower.of_algebraMap_eq
      (R := Poly ι) (S := Poly ι ⊗[ℚ] Poly ι) (A := Rat ι ⊗[ℚ] Poly ι) (by
      intro p
      change algebraMap (Poly ι) (Rat ι) p ⊗ₜ[ℚ] (1 : Poly ι) =
        localizeLeft ι (p ⊗ₜ[ℚ] (1 : Poly ι))
      simp [localizeLeft, polyToRat, IsScalarTower.toAlgHom_apply])
  have hcompat :
      (algebraMap (Poly ι ⊗[ℚ] Poly ι) (Rat ι ⊗[ℚ] Poly ι)).comp
          Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom := by
    apply RingHom.ext
    intro p
    change localizeLeft ι ((1 : Poly ι) ⊗ₜ[ℚ] p) = (1 : Rat ι) ⊗ₜ[ℚ] p
    simp [localizeLeft, polyToRat, IsScalarTower.toAlgHom_apply]
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (Poly ι ⊗[ℚ] Poly ι) (nonZeroDivisors (Poly ι)))
      (Rat ι ⊗[ℚ] Poly ι) :=
    IsLocalization.tensorProduct_tensorProduct ℚ (Poly ι)
      (nonZeroDivisors (Poly ι)) (Rat ι) hcompat
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Algebra.algebraMapSubmonoid (Poly ι ⊗[ℚ] Poly ι) (nonZeroDivisors (Poly ι)))
    (S := Rat ι ⊗[ℚ] Poly ι)
    (halfEmbedding ι).toRingHom
  intro x hx
  have hbase : polynomialEmbedding ι x = 0 := by
    have heq := AlgHom.congr_fun (halfEmbedding_comp_localizeLeft ι) x
    simpa only [AlgHom.comp_apply, RingHom.algebraMap_toAlgebra] using
      heq.symm.trans hx
  have hxzero : x = 0 := (polynomialEmbedding_injective ι)
    (hbase.trans (map_zero (polynomialEmbedding ι)).symm)
  simp [hxzero]

set_option synthInstance.maxHeartbeats 200000 in
/-- The two independent rational-function copies embed faithfully. -/
theorem tensorEmbedding_injective : Function.Injective (tensorEmbedding ι) := by
  let : Algebra (Rat ι ⊗[ℚ] Poly ι) (Rat ι ⊗[ℚ] Rat ι) :=
    (localizeRight ι).toAlgebra
  let : IsScalarTower (Rat ι) (Rat ι ⊗[ℚ] Poly ι) (Rat ι ⊗[ℚ] Rat ι) :=
    IsScalarTower.of_algebraMap_eq
      (R := Rat ι) (S := Rat ι ⊗[ℚ] Poly ι) (A := Rat ι ⊗[ℚ] Rat ι) (by
      intro x
      change x ⊗ₜ[ℚ] (1 : Rat ι) =
        localizeRight ι (x ⊗ₜ[ℚ] (1 : Poly ι))
      simp [localizeRight, polyToRat, IsScalarTower.toAlgHom_apply])
  have hcompat :
      (algebraMap (Rat ι ⊗[ℚ] Poly ι) (Rat ι ⊗[ℚ] Rat ι)).comp
          Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom.comp
          (algebraMap (Poly ι) (Rat ι)) := by
    apply RingHom.ext
    intro p
    change localizeRight ι ((1 : Rat ι) ⊗ₜ[ℚ] p) =
      (1 : Rat ι) ⊗ₜ[ℚ] algebraMap (Poly ι) (Rat ι) p
    simp [localizeRight, polyToRat, IsScalarTower.toAlgHom_apply]
  let : IsLocalization
      ((nonZeroDivisors (Poly ι)).map
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := Rat ι)))
      (Rat ι ⊗[ℚ] Rat ι) :=
    IsLocalization.tensorProduct_tensorProduct_right ℚ (Rat ι)
      (nonZeroDivisors (Poly ι)) (Rat ι) hcompat
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := (nonZeroDivisors (Poly ι)).map
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := Rat ι)))
    (S := Rat ι ⊗[ℚ] Rat ι)
    (tensorEmbedding ι).toRingHom
  intro x hx
  have hhalf : halfEmbedding ι x = 0 := by
    change halfEmbedding ι x = 0 at hx
    exact hx
  have hxzero : x = 0 := (halfEmbedding_injective ι)
    (hhalf.trans (map_zero (halfEmbedding ι)).symm)
  simp [hxzero]

end EuclideanRamsey.IndependentTensor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open scoped TensorProduct

namespace EuclideanRamsey.NineField

open NineGeometry

abbrev ParameterPoly := IndependentTensor.Poly (Fin 9)
abbrev ParameterField := IndependentTensor.Rat (Fin 9)
abbrev TargetPoly := IndependentTensor.JointPoly (Fin 9)
abbrev TargetField := IndependentTensor.JointField (Fin 9)

/-- The rational scalar structure induced by the fraction-ring construction. -/
local instance parameterFieldAlgebra : Algebra ℚ ParameterField :=
  OreLocalization.instAlgebra (R₀ := ℚ) (R := ParameterPoly)
    (S := nonZeroDivisors ParameterPoly)

/-- The rational scalar structure on the joint rational-function field. -/
local instance targetFieldAlgebra : Algebra ℚ TargetField :=
  OreLocalization.instAlgebra (R₀ := ℚ) (R := TargetPoly)
    (S := nonZeroDivisors TargetPoly)

theorem parameterFieldAlgebra_eq_canonical :
    parameterFieldAlgebra = (DivisionRing.toRatAlgebra : Algebra ℚ ParameterField) :=
  Subsingleton.elim _ _

theorem targetFieldAlgebra_eq_canonical :
    targetFieldAlgebra = (DivisionRing.toRatAlgebra : Algebra ℚ TargetField) :=
  Subsingleton.elim _ _

def T (i : Fin 9) : TargetField :=
  algebraMap TargetPoly TargetField (MvPolynomial.X (Sum.inl i))

def U (i : Fin 9) : TargetField :=
  algebraMap TargetPoly TargetField (MvPolynomial.X (Sum.inr i))

/-- The three augmented rational parametrization entries. -/
def a0 : TargetField := 1
def a1 (z : TargetField) : TargetField := (1 - z^2) / (1 + z^2)
def a2 (z : TargetField) : TargetField := (2*z) / (1 + z^2)

def paramVector (z : TargetField) : Option (Fin 2) → TargetField
  | none => a0
  | some j => if j = 0 then a1 z else a2 z

variable (t : Fin 9 → ℝ)

/-- Each parameter is an element of the actual coordinate field, by the
proved recovery formula and coordinate-field equality. -/
def parameter (i : Fin 9) : Coeff (circleConfig t) :=
  ⟨t i, by
    rw [circleConfig_coordinateField]
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)⟩

@[simp] theorem parameter_coe (i : Fin 9) : (parameter t i : ℝ) = t i := rfl

theorem coordinate_zero (i : Fin 9) :
    coordinate (circleConfig t) i 0 =
      (1 - (parameter t i)^2) / (1 + (parameter t i)^2) := by
  apply Subtype.ext
  simp [coordinate, circleConfig, parameter]

theorem coordinate_one (i : Fin 9) :
    coordinate (circleConfig t) i 1 =
      (2 * parameter t i) / (1 + (parameter t i)^2) := by
  have htwo : ((2 : Coeff (circleConfig t)) : ℝ) = 2 :=
    map_ofNat (coordinateField (circleConfig t)).val 2
  apply Subtype.ext
  simp [coordinate, circleConfig, parameter, htwo]

variable (ht : AlgebraicIndependent ℚ t)

/-- The actual coefficient field is identified with the rational function
field using exactly the given algebraic independence of the real parameters. -/
def coefficientEquiv : Coeff (circleConfig t) ≃ₐ[ℚ] ParameterField :=
  (IntermediateField.equivOfEq (circleConfig_coordinateField t)).trans
    ht.aevalEquivField.symm

@[simp] theorem coefficientEquiv_parameter (i : Fin 9) :
    coefficientEquiv t ht (parameter t i) =
      algebraMap ParameterPoly ParameterField (MvPolynomial.X i) := by
  unfold coefficientEquiv
  erw [AlgEquiv.trans_apply, AlgEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  simp [parameter]

def leftCoeff : Coeff (circleConfig t) →ₐ[ℚ] TargetField :=
  (IndependentTensor.leftMap (Fin 9)).comp (coefficientEquiv t ht).toAlgHom

def rightCoeff : Coeff (circleConfig t) →ₐ[ℚ] TargetField :=
  (IndependentTensor.rightMap (Fin 9)).comp (coefficientEquiv t ht).toAlgHom

@[simp] theorem leftCoeff_parameter (i : Fin 9) :
    leftCoeff t ht (parameter t i) = T i := by
  simp [leftCoeff, T]

@[simp] theorem rightCoeff_parameter (i : Fin 9) :
    rightCoeff t ht (parameter t i) = U i := by
  simp [rightCoeff, U]

@[simp] theorem leftCoeff_coordinate_zero (i : Fin 9) :
    leftCoeff t ht (coordinate (circleConfig t) i 0) = a1 (T i) := by
  rw [coordinate_zero]
  simp [a1, map_div₀]

@[simp] theorem leftCoeff_coordinate_one (i : Fin 9) :
    leftCoeff t ht (coordinate (circleConfig t) i 1) = a2 (T i) := by
  rw [coordinate_one]
  simp [a2, map_div₀, map_ofNat]

@[simp] theorem rightCoeff_coordinate_zero (i : Fin 9) :
    rightCoeff t ht (coordinate (circleConfig t) i 0) = a1 (U i) := by
  rw [coordinate_zero]
  simp [a1, map_div₀]

@[simp] theorem rightCoeff_coordinate_one (i : Fin 9) :
    rightCoeff t ht (coordinate (circleConfig t) i 1) = a2 (U i) := by
  rw [coordinate_one]
  simp [a2, map_div₀, map_ofNat]

/-- The tensor equivalence transports both copies of the actual field. -/
def coefficientTensorEquiv :
    TensorRing (circleConfig t) ≃ₐ[ℚ] ParameterField ⊗[ℚ] ParameterField :=
  Algebra.TensorProduct.congr (coefficientEquiv t ht) (coefficientEquiv t ht)

/-- The coordinate-field tensor square embeds in the rational function field
on eighteen variables. -/
def coordinateTensorEmbedding : TensorRing (circleConfig t) →ₐ[ℚ] TargetField :=
  (IndependentTensor.tensorEmbedding (Fin 9)).comp
    (coefficientTensorEquiv t ht).toAlgHom

theorem coordinateTensorEmbedding_injective :
    Function.Injective (coordinateTensorEmbedding t ht) :=
  (IndependentTensor.tensorEmbedding_injective (Fin 9)).comp
    (coefficientTensorEquiv t ht).injective

@[simp] theorem coordinateTensorEmbedding_tmul
    (x y : Coeff (circleConfig t)) :
    coordinateTensorEmbedding t ht (x ⊗ₜ[ℚ] y) =
      leftCoeff t ht x * rightCoeff t ht y := by
  simp [coordinateTensorEmbedding, coefficientTensorEquiv, leftCoeff, rightCoeff]

/-- Exact images of the constant and two spatial augmented coordinates. -/
@[simp] theorem coordinateTensorEmbedding_a0_left (i : Fin 9) :
    coordinateTensorEmbedding t ht
      ((augmented (circleConfig t) i none) ⊗ₜ[ℚ] 1) = a0 := by
  simp [augmented, a0]

@[simp] theorem coordinateTensorEmbedding_a1_left (i : Fin 9) :
    coordinateTensorEmbedding t ht
      ((augmented (circleConfig t) i (some 0)) ⊗ₜ[ℚ] 1) = a1 (T i) := by
  simp [augmented]

@[simp] theorem coordinateTensorEmbedding_a2_left (i : Fin 9) :
    coordinateTensorEmbedding t ht
      ((augmented (circleConfig t) i (some 1)) ⊗ₜ[ℚ] 1) = a2 (T i) := by
  simp [augmented]

@[simp] theorem coordinateTensorEmbedding_a0_right (i : Fin 9) :
    coordinateTensorEmbedding t ht
      (1 ⊗ₜ[ℚ] (augmented (circleConfig t) i none)) = a0 := by
  simp [augmented, a0]

@[simp] theorem coordinateTensorEmbedding_a1_right (i : Fin 9) :
    coordinateTensorEmbedding t ht
      (1 ⊗ₜ[ℚ] (augmented (circleConfig t) i (some 0))) = a1 (U i) := by
  simp [augmented]

@[simp] theorem coordinateTensorEmbedding_a2_right (i : Fin 9) :
    coordinateTensorEmbedding t ht
      (1 ⊗ₜ[ℚ] (augmented (circleConfig t) i (some 1))) = a2 (U i) := by
  simp [augmented]

theorem leftCoeff_augmented (i : Fin 9) (j : Option (Fin 2)) :
    leftCoeff t ht (augmented (circleConfig t) i j) = paramVector (T i) j := by
  cases j with
  | none => simp [augmented, paramVector, a0]
  | some j => fin_cases j <;> simp [augmented, paramVector]

theorem rightCoeff_augmented (i : Fin 9) (j : Option (Fin 2)) :
    rightCoeff t ht (augmented (circleConfig t) i j) = paramVector (U i) j := by
  cases j with
  | none => simp [augmented, paramVector, a0]
  | some j => fin_cases j <;> simp [augmented, paramVector]

/-- The augmented-coordinate tensors map to entries of the rational evaluation matrix. -/
theorem coordinateTensorEmbedding_augmented_tmul (i : Fin 9)
    (α β : Option (Fin 2)) :
    coordinateTensorEmbedding t ht
      ((augmented (circleConfig t) i α) ⊗ₜ[ℚ] (augmented (circleConfig t) i β)) =
      paramVector (T i) α * paramVector (U i) β := by
  rw [coordinateTensorEmbedding_tmul, leftCoeff_augmented, rightCoeff_augmented]

end EuclideanRamsey.NineField

end

end OAI
end
end

section
section
namespace OAI

/-! The denominator-cleared matrix has rows and columns indexed by `Fin 3 × Fin 3`.
At the grid `(0, 1, -1)²`, its polynomial evaluation is a Kronecker square
with nonzero determinant. -/

noncomputable section

namespace EuclideanRamsey.NineGrid

open scoped Kronecker

abbrev Index := Fin 3 × Fin 3
abbrev Vars := Index ⊕ Index
abbrev Poly := MvPolynomial Vars ℚ

/-- The denominator-cleared rational parametrization coordinates. -/
def q {R : Type*} [CommRing R] (z : R) : Fin 3 → R :=
  ![1 + z ^ 2, 1 - z ^ 2, 2 * z]

def T (i : Index) : Poly := MvPolynomial.X (Sum.inl i)
def U (i : Index) : Poly := MvPolynomial.X (Sum.inr i)

/-- Polynomial evaluation rows before dividing by (1+T²)(1+U²). -/
def E : Matrix Index Index Poly :=
  fun i j => q (T i) j.1 * q (U i) j.2

def grid : Fin 3 → ℚ := ![0, 1, -1]

/-- T_(a,b) is sent to grid a, and U_(a,b) to grid b. -/
def gridAssignment : Vars → ℚ
  | Sum.inl i => grid i.1
  | Sum.inr i => grid i.2

def gridEval : Poly →+* ℚ := MvPolynomial.eval gridAssignment

/-- The evaluated one-parameter matrix C'. -/
def C : Matrix (Fin 3) (Fin 3) ℚ := fun i j => q (grid i) j

lemma map_q {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : R) (a : Fin 3) :
    f (q z a) = q (f z) a := by
  fin_cases a <;> simp [q, map_ofNat]

@[simp] lemma gridEval_T (i : Index) : gridEval (T i) = grid i.1 := by
  simp [gridEval, T, gridAssignment]

@[simp] lemma gridEval_U (i : Index) : gridEval (U i) = grid i.2 := by
  simp [gridEval, U, gridAssignment]

/-- Exact rational entries, with rows indexed in the order 0,1,2. -/
lemma C_eq : C = ![![1, 1, 0], ![2, 0, 2], ![2, 0, -2]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> (first | (simp [C, q, grid]; all_goals first | (norm_num [C, q, grid]; done) | rfl | decide) | (norm_num [C, q, grid]; done) | norm_num [C, q, grid])

lemma det_C : Matrix.det C = 8 := by
  rw [Matrix.det_fin_three]
  norm_num [C, q, grid, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- The evaluation is on the polynomial ring alone. -/
lemma evaluated_E : gridEval.mapMatrix E = C ⊗ₖ C := by
  ext i j
  rcases i with ⟨r, s⟩
  rcases j with ⟨a, b⟩
  change gridEval (q (T (r, s)) a * q (U (r, s)) b) = C r a * C s b
  rw [map_mul, map_q, map_q, gridEval_T, gridEval_U]
  rfl

lemma det_evaluated_E : Matrix.det (gridEval.mapMatrix E) = (8 : ℚ) ^ 6 := by
  simp only [evaluated_E, Matrix.det_kronecker, det_C, Fintype.card_fin]
  norm_num

lemma gridEval_det_E : gridEval (Matrix.det E) = (8 : ℚ) ^ 6 := by
  rw [RingHom.map_det]
  exact det_evaluated_E

/-- The full denominator-cleared nine-row polynomial determinant is nonzero. -/
theorem det_E_ne_zero : Matrix.det E ≠ 0 := by
  intro hzero
  have h := gridEval_det_E
  rw [hzero, map_zero] at h
  norm_num at h

end EuclideanRamsey.NineGrid

end

end OAI
end
end

section
section
namespace OAI

/-! Clearing denominators transfers the polynomial determinant to a faithful
rational-function realization. Renaming variables transports the result to
any equivalent set of nine row labels. -/

noncomputable section

namespace EuclideanRamsey.NineRational

abbrev Index := NineGrid.Index
abbrev Poly := NineGrid.Poly
abbrev K := IndependentTensor.JointField Index

/-- Actual rational-coordinate vector, including its constant first entry. -/
def r {F : Type*} [Field F] (z : F) : Fin 3 → F :=
  ![1, (1 - z ^ 2) / (1 + z ^ 2), (2 * z) / (1 + z ^ 2)]

lemma polynomial_denominator_ne_zero (v : NineGrid.Vars) :
    (1 + (MvPolynomial.X v : Poly) ^ 2) ≠ 0 := by
  intro hz
  have h := congrArg (MvPolynomial.eval (fun _ : NineGrid.Vars => (0 : ℚ))) hz
  norm_num at h

lemma mapped_denominator_ne_zero {F : Type*} [Field F]
    (f : Poly →+* F) (hf : Function.Injective f) (v : NineGrid.Vars) :
    1 + f (MvPolynomial.X v) ^ 2 ≠ 0 := by
  intro hz
  apply polynomial_denominator_ne_zero v
  apply hf
  simpa only [map_add, map_one, map_pow, map_zero] using hz

lemma clear_r {F : Type*} [Field F] (z : F) (hz : 1 + z ^ 2 ≠ 0)
    (a : Fin 3) : (1 + z ^ 2) * r z a = NineGrid.q z a := by
  fin_cases a <;> simp [r, NineGrid.q] <;> field_simp [hz]

/-- The actual rational-coordinate matrix in any faithful polynomial realization. -/
def genericMatrix {F : Type*} [Field F] (f : Poly →+* F) : Matrix Index Index F :=
  fun i j => r (f (NineGrid.T i)) j.1 * r (f (NineGrid.U i)) j.2

def rowDenominator {F : Type*} [Field F] (f : Poly →+* F) (i : Index) : F :=
  (1 + f (NineGrid.T i) ^ 2) * (1 + f (NineGrid.U i) ^ 2)

/-- Multiplying each row by its denominator gives the polynomial matrix. -/
lemma cleared_matrix {F : Type*} [Field F] (f : Poly →+* F)
    (hf : Function.Injective f) :
    f.mapMatrix NineGrid.E = Matrix.diagonal (rowDenominator f) * genericMatrix f := by
  ext i j
  rw [Matrix.diagonal_mul]
  change f (NineGrid.q (NineGrid.T i) j.1 * NineGrid.q (NineGrid.U i) j.2) =
    ((1 + f (NineGrid.T i) ^ 2) * (1 + f (NineGrid.U i) ^ 2)) *
      (r (f (NineGrid.T i)) j.1 * r (f (NineGrid.U i)) j.2)
  rw [map_mul, NineGrid.map_q, NineGrid.map_q]
  rw [← clear_r (f (NineGrid.T i)) (mapped_denominator_ne_zero f hf (Sum.inl i)) j.1,
    ← clear_r (f (NineGrid.U i)) (mapped_denominator_ne_zero f hf (Sum.inr i)) j.2]
  ring

/-- The rational-coordinate matrix has nonzero determinant in every faithful realization. -/
theorem det_genericMatrix_ne_zero {F : Type*} [Field F]
    (f : Poly →+* F) (hf : Function.Injective f) :
    Matrix.det (genericMatrix f) ≠ 0 := by
  have hpoly : f (Matrix.det NineGrid.E) ≠ 0 := by
    intro hz
    apply NineGrid.det_E_ne_zero
    apply hf
    simpa only [map_zero] using hz
  have hcleared : Matrix.det (f.mapMatrix NineGrid.E) ≠ 0 := by
    rw [← f.map_det]
    exact hpoly
  intro hz
  apply hcleared
  rw [cleared_matrix f hf, Matrix.det_mul, hz, mul_zero]

/-- The polynomial inclusion into the doubled-variable fraction field. -/
def polynomialInclusion : Poly →+* K := algebraMap Poly K

def t (i : Index) : K := polynomialInclusion (NineGrid.T i)
def u (i : Index) : K := polynomialInclusion (NineGrid.U i)

def M : Matrix Index Index K := fun i j => r (t i) j.1 * r (u i) j.2

theorem det_M_ne_zero : Matrix.det M ≠ 0 :=
  det_genericMatrix_ne_zero polynomialInclusion (IsFractionRing.injective Poly K)

section Relabel

variable {ι : Type*}

/-- Independent rational-function variables with arbitrary row labels. -/
def tVar (i : ι) : IndependentTensor.JointField ι :=
  algebraMap (IndependentTensor.JointPoly ι) (IndependentTensor.JointField ι)
    (MvPolynomial.X (Sum.inl i))

def uVar (i : ι) : IndependentTensor.JointField ι :=
  algebraMap (IndependentTensor.JointPoly ι) (IndependentTensor.JointField ι)
    (MvPolynomial.X (Sum.inr i))

/-- Rename the polynomial variables bijectively and include them in the fraction field. -/
def transportPoly (e : ι ≃ Index) : Poly →+* IndependentTensor.JointField ι :=
  (algebraMap (IndependentTensor.JointPoly ι) (IndependentTensor.JointField ι)).comp
    (MvPolynomial.rename (Equiv.sumCongr e.symm e.symm)).toRingHom

lemma transportPoly_injective (e : ι ≃ Index) : Function.Injective (transportPoly e) :=
  (IsFractionRing.injective (IndependentTensor.JointPoly ι)
    (IndependentTensor.JointField ι)).comp
      (MvPolynomial.rename_injective (Equiv.sumCongr e.symm e.symm)
        (Equiv.sumCongr e.symm e.symm).injective)

/-- Both axes are reindexed by e. Columns encode the two coordinate indices. -/
def transportedMatrix (e : ι ≃ Index) : Matrix ι ι (IndependentTensor.JointField ι) :=
  (genericMatrix (transportPoly e)).submatrix e e

lemma transportedMatrix_apply (e : ι ≃ Index) (i j : ι) :
    transportedMatrix e i j = r (tVar i) (e j).1 * r (uVar i) (e j).2 := by
  simp [transportedMatrix, genericMatrix, transportPoly, NineGrid.T, NineGrid.U,
    tVar, uVar]

theorem det_transportedMatrix_ne_zero [Fintype ι] [DecidableEq ι] (e : ι ≃ Index) :
    Matrix.det (transportedMatrix e) ≠ 0 := by
  change Matrix.det ((genericMatrix (transportPoly e)).submatrix e e) ≠ 0
  rw [Matrix.det_submatrix_equiv_self]
  exact det_genericMatrix_ne_zero (transportPoly e) (transportPoly_injective e)

end Relabel

/-- Concrete row/column enumeration of the nine tensor coordinates. -/
def fin9Equiv : Fin 9 ≃ Index := (finProdFinEquiv : Index ≃ Fin (3 * 3)).symm

def fin9Matrix : Matrix (Fin 9) (Fin 9) (IndependentTensor.JointField (Fin 9)) :=
  transportedMatrix fin9Equiv

lemma fin9Matrix_apply (i j : Fin 9) :
    fin9Matrix i j = r (tVar i) (fin9Equiv j).1 * r (uVar i) (fin9Equiv j).2 :=
  transportedMatrix_apply fin9Equiv i j

theorem det_fin9Matrix_ne_zero : Matrix.det fin9Matrix ≠ 0 :=
  det_transportedMatrix_ne_zero fin9Equiv

end EuclideanRamsey.NineRational

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

theorem singleton_ramsey {d : ℕ} (a : Fin 1 → Space d) : Ramsey a := by
  intro r hr
  refine ⟨1, by omega, ?_⟩
  intro c
  refine ⟨fun _ => 0, ?_, c 0, ?_⟩
  · intro i j
    have : i = j := Subsingleton.elim _ _
    simp [this]
  · intro i
    rfl

theorem ramsey_congruent_iff {s d D : ℕ} {a : Fin s → Space d}
    {b : Fin s → Space D} (h : Congruent a b) : Ramsey a ↔ Ramsey b := by
  constructor
  · intro ha r hr
    obtain ⟨n, hn, hn'⟩ := ha r hr
    refine ⟨n, hn, fun c => ?_⟩
    obtain ⟨x, hx, k, hk⟩ := hn' c
    exact ⟨x, fun i j => (hx i j).trans (h i j).symm, k, hk⟩
  · intro ha r hr
    obtain ⟨n, hn, hn'⟩ := ha r hr
    refine ⟨n, hn, fun c => ?_⟩
    obtain ⟨x, hx, k, hk⟩ := hn' c
    exact ⟨x, fun i j => (hx i j).trans (h i j), k, hk⟩

theorem linearIsometry_of_equal_gram {ι : Type uIndex} {E : Type uDomain} {F : Type uCodomain} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : ι → E) (y : ι → F)
    (hspan : Submodule.span ℝ (Set.range x) = ⊤)
    (hgram : ∀ i j, ⟪y i, y j⟫ = ⟪x i, x j⟫) :
    ∃ Q : E →ₗᵢ[ℝ] F, ∀ i, Q (x i) = y i := by
  classical
  let A := Fintype.linearCombination ℝ x
  let B := Fintype.linearCombination ℝ y
  have hinner (c e : ι → ℝ) : ⟪B c, B e⟫ = ⟪A c, A e⟫ := by
    simp only [A, B, Fintype.linearCombination_apply, sum_inner, inner_sum,
      real_inner_smul_left, inner_smul_right, hgram]
  have hnorm (c : ι → ℝ) : ‖B c‖ = ‖A c‖ := by
    have h := hinner c c
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (B c), norm_nonneg (A c)]
  have hsurj : LinearMap.range A = ⊤ := by
    rw [Fintype.range_linearCombination]
    exact hspan
  obtain ⟨R, hR⟩ := A.exists_rightInverse_of_surjective hsurj
  have hR' (z : E) : A (R z) = z := congrArg (fun L : E →ₗ[ℝ] E => L z) hR
  let L : E →ₗ[ℝ] F := B.comp R
  have hLnorm (z : E) : ‖L z‖ = ‖z‖ := by
    change ‖B (R z)‖ = ‖z‖
    rw [hnorm, hR']
  have hfactor (c : ι → ℝ) : L (A c) = B c := by
    have hzero : A (R (A c) - c) = 0 := by rw [map_sub, hR', sub_self]
    have : B (R (A c) - c) = 0 := by
      apply norm_eq_zero.mp
      rw [hnorm, hzero, norm_zero]
    simpa only [map_sub, L, LinearMap.comp_apply, sub_eq_zero] using this
  refine ⟨⟨L, hLnorm⟩, ?_⟩
  intro i
  simpa [A, B] using hfactor (Pi.single i 1)

theorem congruent_linearIsometry {s d D : ℕ} (a : Fin s → Space d)
    (b : Fin s → Space D) (i₀ : Fin s)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) (h : Congruent a b) :
    ∃ Q : Space d →ₗᵢ[ℝ] Space D, ∃ t : Space D, ∀ i, b i = t + Q (a i) := by
  have hv : vectorSpan ℝ (Set.range a) = ⊤ := by
    simpa only [direction_affineSpan, AffineSubspace.direction_top] using
      congrArg AffineSubspace.direction hspan
  have hs : Submodule.span ℝ (Set.range fun i => a i - a i₀) = ⊤ := by
    rw [vectorSpan_range_eq_span_range_vsub_right ℝ a i₀] at hv
    exact hv
  have hg (i j : Fin s) : ⟪b i - b i₀, b j - b i₀⟫ =
      ⟪a i - a i₀, a j - a i₀⟫ := by
    simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      sub_sub_sub_cancel_right, ← dist_eq_norm]
    rw [h i i₀, h j i₀, h i j]
  obtain ⟨Q, hQ⟩ := linearIsometry_of_equal_gram
    (fun i => a i - a i₀) (fun i => b i - b i₀) hs hg
  refine ⟨Q, b i₀ - Q (a i₀), fun i => ?_⟩
  have hi := hQ i
  rw [map_sub] at hi
  calc
    b i = (b i - b i₀) + b i₀ := (sub_add_cancel _ _).symm
    _ = (Q (a i) - Q (a i₀)) + b i₀ := by rw [hi]
    _ = b i₀ - Q (a i₀) + Q (a i) := by abel

end EuclideanRamsey

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

private theorem sum_floor_bounds {s : ℕ} (hs : 0 < s) (f : Fin s → ℝ) :
    (∑ i, f i) - s < ((∑ i, ⌊f i⌋ : ℤ) : ℝ) ∧
    ((∑ i, ⌊f i⌋ : ℤ) : ℝ) ≤ ∑ i, f i := by
  have hu : (Finset.univ : Finset (Fin s)).Nonempty := ⟨⟨0, hs⟩, Finset.mem_univ _⟩
  have hlt := Finset.sum_lt_sum_of_nonempty hu (fun i _ => Int.lt_floor_add_one (f i))
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Int.floor_le (f i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hlt
  constructor
  · push_cast
    linarith
  · simpa only [Int.cast_sum] using hle

theorem floor_coloring_obstruction {X : Type uPoint} {s : ℕ} (hs : 0 < s)
    (H : Fin s → X → ℝ) (hcancel : ∀ z, ∑ i, H i z = 0)
    (b : Fin s → X)
    (hmono : ∀ i, (fun j : Fin s =>
      (⌊((2 * s + 1 : ℕ) : ℝ) / 2 * H j (b i)⌋ : ZMod (2 * s + 1))) =
      (fun j : Fin s =>
      (⌊((2 * s + 1 : ℕ) : ℝ) / 2 * H j (b ⟨0, hs⟩)⌋ : ZMod (2 * s + 1)))) :
    ∑ i, H i (b i) ≠ -1 := by
  intro hsum
  let K : ℕ := 2 * s + 1
  let x : Fin s → ℝ := fun i => (K : ℝ) / 2 * H i (b i)
  let y : Fin s → ℝ := fun i => (K : ℝ) / 2 * H i (b ⟨0, hs⟩)
  have hx : ∑ i, x i = -(K : ℝ) / 2 := by
    simp [x, ← Finset.mul_sum, hsum] <;> ring
  have hy : ∑ i, y i = 0 := by
    simp [y, ← Finset.mul_sum, hcancel]
  let A : ℤ := ∑ i, ⌊x i⌋
  let B : ℤ := ∑ i, ⌊y i⌋
  have hAB : (A : ZMod K) = (B : ZMod K) := by
    simp only [A, B, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (hmono i) i
  have hdvd : (K : ℤ) ∣ B - A := (ZMod.intCast_eq_intCast_iff_dvd_sub A B K).mp hAB
  obtain ⟨hxlo, hxhi⟩ := sum_floor_bounds hs x
  obtain ⟨hylo, hyhi⟩ := sum_floor_bounds hs y
  change (∑ i, x i) - s < (A : ℝ) at hxlo
  change (A : ℝ) ≤ ∑ i, x i at hxhi
  change (∑ i, y i) - s < (B : ℝ) at hylo
  change (B : ℝ) ≤ ∑ i, y i at hyhi
  rw [hx] at hxlo hxhi
  rw [hy] at hylo hyhi
  have hK : (K : ℝ) = 2 * (s : ℝ) + 1 := by simp [K]
  have hpos : (0 : ℤ) < B - A := by
    have : (0 : ℝ) < (B : ℝ) - (A : ℝ) := by linarith
    exact_mod_cast this
  have hlt : B - A < (K : ℤ) := by
    have : (B : ℝ) - (A : ℝ) < (K : ℝ) := by linarith
    exact_mod_cast this
  exact (not_le_of_gt hlt) (Int.le_of_dvd hpos hdvd)

abbrev RealTensor := ℝ ⊗[ℚ] ℝ
abbrev RealArray (d : ℕ) := Matrix (Option (Fin d)) (Option (Fin d)) RealTensor
abbrev SeparationSpace (s d : ℕ) := (Fin s → RealTensor) × Matrix (Fin d) (Fin d) ℝ

def realAugmented {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : Option (Fin d) → ℝ
  | none => 1
  | some j => a i j

def arrayEvaluation {s d : ℕ} (a : Fin s → Space d) (i : Fin s) :
    RealArray d →ₗ[ℚ] RealTensor where
  toFun P := ∑ α, ∑ β, ((realAugmented a i α) ⊗ₜ[ℚ] (1 : ℝ)) * P α β *
    ((1 : ℝ) ⊗ₜ[ℚ] (realAugmented a i β))
  map_add' P Q := by
    simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' q P := by
    simp only [Matrix.smul_apply, RingHom.id_apply, mul_smul_comm, smul_mul_assoc,
      Finset.smul_sum]

def spatialMultiply {d : ℕ} : RealArray d →ₗ[ℚ] Matrix (Fin d) (Fin d) ℝ where
  toFun P := fun α β => Algebra.TensorProduct.lmul' ℚ (P (some α) (some β))
  map_add' P Q := by
    ext α β
    exact map_add (Algebra.TensorProduct.lmul' ℚ) _ _
  map_smul' q P := by
    ext α β
    exact (Algebra.TensorProduct.lmul' ℚ).toLinearMap.map_smul q _

def arrayMap {s d : ℕ} (a : Fin s → Space d) :
    RealArray d →ₗ[ℚ] SeparationSpace s d :=
  (LinearMap.pi (arrayEvaluation a)).prod spatialMultiply

def RealCriterion {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∃ P : RealArray d, (∀ i, arrayEvaluation a i P = 0) ∧ spatialMultiply P = 1

theorem separate_arrayMap {s d : ℕ} (a : Fin s → Space d) (h : ¬ RealCriterion a) :
    ∃ ℓ : SeparationSpace s d →ₗ[ℚ] ℝ,
      (∀ P, ℓ (arrayMap a P) = 0) ∧ ℓ (0, 1) = 1 := by
  let N := LinearMap.range (arrayMap a)
  have hy : (0, 1) ∉ N := by
    rintro ⟨P, hP⟩
    apply h
    refine ⟨P, ?_, ?_⟩
    · intro i
      exact congrFun (congrArg Prod.fst hP) i
    · exact congrArg Prod.snd hP
  have hq : N.mkQ (0, 1) ≠ 0 := by
    intro hz
    exact hy ((Submodule.Quotient.mk_eq_zero N).mp hz)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ hq
  let ℓ : SeparationSpace s d →ₗ[ℚ] ℝ :=
    (Algebra.linearMap ℚ ℝ).comp (f.comp N.mkQ)
  refine ⟨ℓ, ?_, ?_⟩
  · intro P
    have hp : N.mkQ (arrayMap a P) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero N).mpr
      exact ⟨P, rfl⟩
    simp [ℓ, hp]
  · change ((f (N.mkQ (0, 1)) : ℚ) : ℝ) = 1
    rw [hf]
    norm_num

def diagonalArray {d : ℕ} (v : ℝ) (u : Space d) : RealArray d :=
  let w : Option (Fin d) → ℝ := fun α => α.elim v (u ·)
  fun α β => w α ⊗ₜ[ℚ] w β

def gradientRankOne {d : ℕ} (u : Space d) : Matrix (Fin d) (Fin d) ℝ :=
  fun α β => u α * u β

def affineEvaluation {s d : ℕ} (a : Fin s → Space d) (i : Fin s)
    (v : ℝ) (u : Space d) : ℝ := v + ∑ j, a i j * u j

lemma arrayEvaluation_diagonal {s d : ℕ} (a : Fin s → Space d) (i : Fin s)
    (v : ℝ) (u : Space d) :
    arrayEvaluation a i (diagonalArray v u) =
      affineEvaluation a i v u ⊗ₜ[ℚ] affineEvaluation a i v u := by
  let w : Option (Fin d) → ℝ := fun α => α.elim v (u ·)
  have he : affineEvaluation a i v u = ∑ α, realAugmented a i α * w α := by
    simp [affineEvaluation, realAugmented, w, Fintype.sum_option]
  rw [he, TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum]
  change (∑ α, ∑ β, (realAugmented a i α ⊗ₜ[ℚ] (1 : ℝ)) *
    (w α ⊗ₜ[ℚ] w β) * ((1 : ℝ) ⊗ₜ[ℚ] realAugmented a i β)) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,  mul_comm]

lemma spatialMultiply_diagonal {d : ℕ} (v : ℝ) (u : Space d) :
    spatialMultiply (diagonalArray v u) = gradientRankOne u := by
  ext α β
  change (Algebra.TensorProduct.lmul' ℚ) (u α ⊗ₜ[ℚ] u β) = u α * u β
  simp

theorem exists_separated_functions {s d : ℕ} (a : Fin s → Space d)
    (h : ¬ RealCriterion a) :
    ∃ f : Fin s → ℝ → ℝ, ∃ L : Matrix (Fin d) (Fin d) ℝ →ₗ[ℚ] ℝ,
      L 1 = 1 ∧
      (∀ v u, (∑ i, f i (affineEvaluation a i v u)) + L (gradientRankOne u) = 0) ∧
      ∀ x, ∑ i, f i x = 0 := by
  classical
  obtain ⟨ℓ, hℓ, hℓ₀⟩ := separate_arrayMap a h
  let f : Fin s → ℝ → ℝ := fun i x => ℓ (Pi.single i (x ⊗ₜ[ℚ] x), 0)
  let L : Matrix (Fin d) (Fin d) ℝ →ₗ[ℚ] ℝ := ℓ.comp (LinearMap.inr ℚ _ _)
  have hsplit (x : Fin s → RealTensor) (M : Matrix (Fin d) (Fin d) ℝ) :
      ℓ (x, M) = (∑ i, ℓ (Pi.single i (x i), 0)) + L M := by
    change ℓ (x, M) = (∑ i, ℓ (Pi.single i (x i), 0)) + ℓ (0, M)
    rw [← map_sum, ← map_add]
    congr 1
    ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  have heq (v : ℝ) (u : Space d) :
      (∑ i, f i (affineEvaluation a i v u)) + L (gradientRankOne u) = 0 := by
    have hp := hℓ (diagonalArray v u)
    change ℓ ((fun i => arrayEvaluation a i (diagonalArray v u)),
      spatialMultiply (diagonalArray v u)) = 0 at hp
    simp only [arrayEvaluation_diagonal, spatialMultiply_diagonal] at hp
    rw [hsplit] at hp
    exact hp
  refine ⟨f, L, hℓ₀, heq, ?_⟩
  intro x
  have hz : gradientRankOne (0 : Space d) = 0 := by ext; simp [gradientRankOne]
  simpa [affineEvaluation, hz] using heq x (0 : Space d)

def isometryRows {d D : ℕ} (Q : Space d →ₗᵢ[ℝ] Space D) (j : Fin D) : Space d :=
  WithLp.toLp 2 (fun α => Q (EuclideanSpace.single α 1) j)

lemma isometryRows_apply {d D : ℕ} (Q : Space d →ₗᵢ[ℝ] Space D)
    (x : Space d) (j : Fin D) :
    Q x j = ∑ α, x α * isometryRows Q j α := by
  have hx := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
  have hv := congrArg (fun z : Space d => Q z j) hx
  simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    isometryRows, WithLp.ofLp_toLp] using hv.symm

lemma isometryRows_gram {d D : ℕ} (Q : Space d →ₗᵢ[ℝ] Space D)
    (α β : Fin d) :
    ∑ j, isometryRows Q j α * isometryRows Q j β = if α = β then 1 else 0 := by
  have h := Q.inner_map_map (EuclideanSpace.single β 1) (EuclideanSpace.single α 1)
  rw [EuclideanSpace.inner_single_left] at h
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, map_one, one_mul,
    PiLp.single_apply, eq_comm, isometryRows, WithLp.ofLp_toLp] using h

theorem separated_copy_sum {s d D : ℕ} (a : Fin s → Space d)
    (f : Fin s → ℝ → ℝ) (L : Matrix (Fin d) (Fin d) ℝ →ₗ[ℚ] ℝ)
    (hL : L 1 = 1)
    (heq : ∀ v u, (∑ i, f i (affineEvaluation a i v u)) + L (gradientRankOne u) = 0)
    (Q : Space d →ₗᵢ[ℝ] Space D) (t : Space D) :
    ∑ i, ∑ j, f i ((t + Q (a i)) j) = -1 := by
  have hrows : (∑ j, gradientRankOne (isometryRows Q j)) = (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext α β
    simp only [Matrix.sum_apply, gradientRankOne, Matrix.one_apply, isometryRows_gram]
  have heach (j : Fin D) :
      (∑ i, f i ((t + Q (a i)) j)) = -L (gradientRankOne (isometryRows Q j)) := by
    have h := heq (t j) (isometryRows Q j)
    apply eq_neg_of_add_eq_zero_left
    convert h using 2
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [PiLp.add_apply, affineEvaluation, isometryRows_apply]
  rw [Finset.sum_comm]
  simp only [heach, Finset.sum_neg_distrib, ← map_sum, hrows, hL]

theorem ramsey_realCriterion {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hR : Ramsey a) : RealCriterion a := by
  classical
  by_contra h
  obtain ⟨f, L, hL, heq, hcancel⟩ := exists_separated_functions a h
  let K := 2 * s + 1
  let Colors := Fin s → ZMod K
  have hK : 1 < K := by dsimp [K]; omega
  have hr : 2 ≤ Fintype.card Colors := by
    change 2 ≤ Fintype.card (Fin s → ZMod K)
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    exact Nat.one_lt_pow (by omega) hK
  obtain ⟨D, hD, hD'⟩ := hR (Fintype.card Colors) hr
  let H : Fin s → Space D → ℝ := fun i z => ∑ j, f i (z j)
  have hH (z : Space D) : ∑ i, H i z = 0 := by
    simp only [H]
    rw [Finset.sum_comm]
    simp only [hcancel, Finset.sum_const_zero]
  let color : Space D → Colors := fun z i => (⌊(K : ℝ) / 2 * H i z⌋ : ZMod K)
  obtain ⟨b, hb, k, hk⟩ := hD' (fun z => Fintype.equivFin Colors (color z))
  have hmono : ∀ i, color (b i) = color (b ⟨0, hs⟩) := by
    intro i
    apply (Fintype.equivFin Colors).injective
    exact (hk i).trans (hk ⟨0, hs⟩).symm
  have hnot := floor_coloring_obstruction hs H hH b hmono
  apply hnot
  obtain ⟨Q, t, hQ⟩ := congruent_linearIsometry a b ⟨0, hs⟩ hspan hb
  simp only [H, hQ]
  exact separated_copy_sum a f L hL heq Q t

end EuclideanRamsey

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

section Descent
variable (F : IntermediateField ℚ ℝ) {ι : Type uIndex} (b : Module.Basis ι F ℝ)

def tensorCoordinates : (ℝ ⊗[ℚ] ℝ) ≃ₗ[ℚ] (ι × ι →₀ (F ⊗[ℚ] F)) :=
  (TensorProduct.congr (b.repr.restrictScalars ℚ) (b.repr.restrictScalars ℚ)).trans
    (finsuppTensorFinsupp ℚ ℚ F F ι ι)

lemma tensorCoordinates_tmul (x y : ℝ) (k : ι × ι) :
    tensorCoordinates F b (x ⊗ₜ[ℚ] y) k = b.repr x k.1 ⊗ₜ[ℚ] b.repr y k.2 := by
  rcases k with ⟨l, m⟩
  simp [tensorCoordinates]

lemma tensorCoordinates_symm_single_tmul (x y : F) (k : ι × ι) :
    (tensorCoordinates F b).symm (Finsupp.single k (x ⊗ₜ[ℚ] y)) =
      (x • b k.1) ⊗ₜ[ℚ] (y • b k.2) := by
  simp [tensorCoordinates, finsuppTensorFinsupp_symm_single]

lemma repr_mul (x : F) (u : ℝ) :
    b.repr ((x : ℝ) * u) = x • b.repr u := by
  simpa only [Algebra.smul_def, IntermediateField.algebraMap_apply] using b.repr.map_smul x u

lemma tensorCoordinates_sandwich (x y : F) (T : ℝ ⊗[ℚ] ℝ) :
    tensorCoordinates F b (((x : ℝ) ⊗ₜ[ℚ] (1 : ℝ)) * T *
      ((1 : ℝ) ⊗ₜ[ℚ] (y : ℝ))) =
      (x ⊗ₜ[ℚ] y) • tensorCoordinates F b T := by
  ext k
  induction T using OAI.tensorInductionOn with
  | tmul u v =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      tensorCoordinates_tmul, Finsupp.smul_apply, smul_eq_mul]
    rw [repr_mul, mul_comm v (y : ℝ), repr_mul]
    simp only [Finsupp.smul_apply, smul_eq_mul]
  | add U V hU hV =>
    simpa only [mul_add, add_mul, map_add, Finsupp.add_apply, smul_add,
      Finsupp.smul_apply] using congrArg₂ (· + ·) hU hV

variable (φ : ℝ →ₗ[F] F)

local instance tensorRing : CommRing (F ⊗[ℚ] F) := inferInstance

def coefficientTrace : (ι × ι →₀ (F ⊗[ℚ] F)) →ₗ[(F ⊗[ℚ] F)] (F ⊗[ℚ] F) :=
  Finsupp.linearCombination (F ⊗[ℚ] F) (fun k => φ (b k.1 * b k.2) ⊗ₜ[ℚ] (1 : F))

def tensorDescent : (ℝ ⊗[ℚ] ℝ) →ₗ[ℚ] (F ⊗[ℚ] F) :=
  ((coefficientTrace F b φ).restrictScalars ℚ).comp (tensorCoordinates F b).toLinearMap

lemma tensorDescent_sandwich (x y : F) (T : ℝ ⊗[ℚ] ℝ) :
    tensorDescent F b φ (((x : ℝ) ⊗ₜ[ℚ] (1 : ℝ)) * T *
      ((1 : ℝ) ⊗ₜ[ℚ] (y : ℝ))) =
      (x ⊗ₜ[ℚ] (1 : F)) * tensorDescent F b φ T * ((1 : F) ⊗ₜ[ℚ] y) := by
  change coefficientTrace F b φ (tensorCoordinates F b _) = _
  rw [tensorCoordinates_sandwich, map_smul]
  change (x ⊗ₜ[ℚ] y) * tensorDescent F b φ T = _
  rw [mul_right_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

lemma coefficientTrace_multiply (z : ι × ι →₀ (F ⊗[ℚ] F)) :
    Algebra.TensorProduct.lmul' ℚ (coefficientTrace F b φ z) =
      φ (Algebra.TensorProduct.lmul' ℚ ((tensorCoordinates F b).symm z)) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single k z =>
    induction z using OAI.tensorInductionOn with
    | add z w hz hw => simp only [Finsupp.single_add, map_add, hz, hw]
    | tmul x y =>
      simp only [coefficientTrace, Finsupp.linearCombination_single, smul_eq_mul,
        map_mul, Algebra.TensorProduct.lmul'_apply_tmul, mul_one,
        tensorCoordinates_symm_single_tmul]
      have hmul : (x • b k.1) * (y • b k.2) = (x * y) • (b k.1 * b k.2) := by
        simp only [Algebra.smul_def, map_mul]
        ring
      rw [hmul, map_smul, smul_eq_mul]

lemma tensorDescent_multiply (T : ℝ ⊗[ℚ] ℝ) :
    Algebra.TensorProduct.lmul' ℚ (tensorDescent F b φ T) =
      φ (Algebra.TensorProduct.lmul' ℚ T) := by
  change Algebra.TensorProduct.lmul' ℚ (coefficientTrace F b φ (tensorCoordinates F b T)) = _
  rw [coefficientTrace_multiply, LinearEquiv.symm_apply_apply]

end Descent

theorem realCriterion_fieldCriterion {s d : ℕ} (a : Fin s → Space d)
    (h : RealCriterion a) : FieldCriterion a := by
  classical
  let F := coordinateField a
  let b := Module.Free.chooseBasis F ℝ
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : ℝ) ≠ 0)
  let δ := tensorDescent F b φ
  obtain ⟨P, he, hm⟩ := h
  refine ⟨fun α β => δ (P α β), ?_, ?_⟩
  · intro i
    have haug (α : Option (Fin d)) : ((augmented a i α : F) : ℝ) = realAugmented a i α := by
      cases α <;> rfl
    have hd := congrArg δ (he i)
    change δ (∑ α, ∑ β, (realAugmented a i α ⊗ₜ[ℚ] (1 : ℝ)) * P α β *
      ((1 : ℝ) ⊗ₜ[ℚ] realAugmented a i β)) = δ 0 at hd
    simp only [map_sum, map_zero] at hd
    simpa only [δ, ← haug, tensorDescent_sandwich] using hd
  · intro α β
    change Algebra.TensorProduct.lmul' ℚ (tensorDescent F b φ (P (some α) (some β))) = _
    rw [tensorDescent_multiply]
    have hab := congrFun (congrFun hm α) β
    change Algebra.TensorProduct.lmul' ℚ (P (some α) (some β)) = _ at hab
    rw [hab]
    by_cases heq : α = β
    · simp only [Matrix.one_apply, heq, ite_true, if_true, hφ]
    · simp only [Matrix.one_apply, heq, ite_false, if_false, map_zero]

theorem ramsey_fieldCriterion {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hR : Ramsey a) : FieldCriterion a :=
  realCriterion_fieldCriterion a (ramsey_realCriterion a hs hspan hR)

end EuclideanRamsey

namespace EuclideanRamsey
open scoped TensorProduct BigOperators

theorem fieldCriterion_realCriterion {s d : ℕ} (a : Fin s → Space d)
    (h : FieldCriterion a) : RealCriterion a := by
  classical
  obtain ⟨P,hP,hG⟩ := h
  let φ : TensorRing a →ₐ[ℚ] RealTensor :=
    Algebra.TensorProduct.map (coordinateField a).val (coordinateField a).val
  have haug (i : Fin s) (α : Option (Fin d)) :
      ((augmented a i α : Coeff a) : ℝ) = realAugmented a i α := by
    cases α <;> rfl
  have hmul (T : TensorRing a) :
      Algebra.TensorProduct.lmul' ℚ (φ T) = (multiply a T : ℝ) := by
    induction T using OAI.tensorInductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp [hx,hy]
  refine ⟨fun α β => φ (P α β),?_,?_⟩
  · intro i
    have hh := congrArg φ (hP i)
    have hφ (x y : Coeff a) : φ (x ⊗ₜ[ℚ] y) = (x:ℝ) ⊗ₜ[ℚ] (y:ℝ) := rfl
    change (∑ α,∑ β,(realAugmented a i α ⊗ₜ[ℚ] (1:ℝ))*φ (P α β)*
      ((1:ℝ) ⊗ₜ[ℚ] realAugmented a i β)) = 0
    simpa only [map_sum,map_mul,map_zero,hφ,haug,OneMemClass.coe_one] using hh
  · ext α β
    change Algebra.TensorProduct.lmul' ℚ (φ (P (some α) (some β))) = _
    rw [hmul,hG]
    simp only [Matrix.one_apply]
    split_ifs <;> rfl

end EuclideanRamsey

end

end OAI
end
end

section
section
namespace OAI

/-! Nonsingular tensor evaluation matrices obstruct the Euclidean Ramsey property. -/

noncomputable section
open scoped TensorProduct BigOperators

namespace EuclideanRamsey.NineLinearObstruction

theorem vector_eq_zero_of_det_ne_zero {J K : Type*} [Fintype J]
    [DecidableEq J] [Field K] (M : Matrix J J K) (hM : M.det ≠ 0)
    (v : J → K) (hv : M.mulVec v = 0) : v = 0 := by
  have hu : IsUnit M := M.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hM)
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hu)
  simpa using hv

abbrev Column (d : ℕ) := Option (Fin d) × Option (Fin d)

/-- Rows are reindexed by an actual equivalence; entries are the exact
images of the two augmented-coordinate tensor factors in FieldCriterion. -/
def evaluationMatrix {s d : ℕ} (a : Fin s → Space d)
    {K : Type*} [Field K] [Algebra ℚ K]
    (f : TensorRing a →ₐ[ℚ] K) (e : Column d ≃ Fin s) :
    Matrix (Column d) (Column d) K := fun i q =>
  f ((augmented a (e i) q.1) ⊗ₜ[ℚ] (1 : Coeff a)) *
    f ((1 : Coeff a) ⊗ₜ[ℚ] (augmented a (e i) q.2))

theorem not_fieldCriterion_of_det_ne_zero {s d : ℕ} (a : Fin s → Space d)
    (hd : 0 < d) {K : Type*} [Field K] [Algebra ℚ K]
    (f : TensorRing a →ₐ[ℚ] K) (hf : Function.Injective f)
    (e : Column d ≃ Fin s) (hdet : (evaluationMatrix a f e).det ≠ 0) :
    ¬ FieldCriterion a := by
  classical
  rintro ⟨P, hP, hspatial⟩
  let v : Column d → K := fun q => f (P q.1 q.2)
  have hv : (evaluationMatrix a f e).mulVec v = 0 := by
    funext i
    have h := congrArg f (hP (e i))
    simp only [map_sum, map_mul, map_zero] at h
    change (∑ q : Column d, evaluationMatrix a f e i q * v q) = 0
    rw [Fintype.sum_prod_type]
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro α hα
    apply Finset.sum_congr rfl
    intro β hβ
    dsimp [evaluationMatrix, v]
    ring
  have hvzero := vector_eq_zero_of_det_ne_zero (evaluationMatrix a f e) hdet v hv
  have hPzero (α β : Option (Fin d)) : P α β = 0 := by
    apply hf
    have h := congrFun hvzero (α, β)
    simpa only [v, Pi.zero_apply, map_zero] using h
  let j : Fin d := ⟨0, hd⟩
  have hbad := hspatial j j
  rw [hPzero, map_zero, ite_eq_left rfl] at hbad
  exact zero_ne_one hbad

/-- Ramsey configurations cannot have a nonsingular tensor evaluation matrix. -/
theorem not_ramsey_of_det_ne_zero {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (hd : 0 < d)
    (hspan : affineSpan ℝ (Set.range a) = ⊤)
    {K : Type*} [Field K] [Algebra ℚ K]
    (f : TensorRing a →ₐ[ℚ] K) (hf : Function.Injective f)
    (e : Column d ≃ Fin s) (hdet : (evaluationMatrix a f e).det ≠ 0) :
    ¬ Ramsey a := by
  intro hR
  exact not_fieldCriterion_of_det_ne_zero a hd f hf e hdet
    (ramsey_fieldCriterion a hs hspan hR)

end EuclideanRamsey.NineLinearObstruction

end

end OAI
end
end

section
section
namespace OAI

/-! Nine algebraically independent circle parameters give a non-Ramsey configuration. -/

noncomputable section
namespace EuclideanRamsey.NineMain

local instance parameterFieldAlgebra : Algebra ℚ NineField.ParameterField :=
  NineField.parameterFieldAlgebra

local instance targetFieldAlgebra : Algebra ℚ NineField.TargetField :=
  NineField.targetFieldAlgebra

open NineGeometry
open scoped TensorProduct

def gridToFin9 : NineGrid.Index ≃ Fin 9 := finProdFinEquiv

def gridToColumn : NineGrid.Index ≃ NineLinearObstruction.Column 2 :=
  Equiv.prodCongr (finSuccEquiv 2) (finSuccEquiv 2)

def rowEquiv : NineLinearObstruction.Column 2 ≃ Fin 9 :=
  gridToColumn.symm.trans gridToFin9

/-- Renaming the polynomial variables into the independent-variable field. -/
def polynomialEmbedding : NineGrid.Poly →+* NineField.TargetField :=
  (algebraMap NineField.TargetPoly NineField.TargetField).comp
    (MvPolynomial.renameEquiv ℚ (Equiv.sumCongr gridToFin9 gridToFin9)).toRingHom

theorem polynomialEmbedding_injective : Function.Injective polynomialEmbedding :=
  (IsFractionRing.injective NineField.TargetPoly NineField.TargetField).comp
    (MvPolynomial.renameEquiv ℚ (Equiv.sumCongr gridToFin9 gridToFin9)).injective

@[simp] theorem polynomialEmbedding_T (i : NineGrid.Index) :
    polynomialEmbedding (NineGrid.T i) = NineField.T (gridToFin9 i) := by
  simp [polynomialEmbedding, NineGrid.T, NineField.T]

@[simp] theorem polynomialEmbedding_U (i : NineGrid.Index) :
    polynomialEmbedding (NineGrid.U i) = NineField.U (gridToFin9 i) := by
  simp [polynomialEmbedding, NineGrid.U, NineField.U]

theorem paramVector_eq_r (z : NineField.TargetField) (a : Option (Fin 2)) :
    NineField.paramVector z a = NineRational.r z ((finSuccEquiv 2).symm a) := by
  cases a with
  | none => simp [NineField.paramVector, NineField.a0, NineRational.r]
  | some a => fin_cases a <;>
      simp [NineField.paramVector, NineField.a1, NineField.a2, NineRational.r]

/-- The tensor evaluation matrix is the rational-coordinate matrix after reindexing. -/
theorem evaluationMatrix_eq (t : Fin 9 → ℝ) (ht : AlgebraicIndependent ℚ t) :
    NineLinearObstruction.evaluationMatrix (circleConfig t)
      (NineField.coordinateTensorEmbedding t ht) rowEquiv =
    Matrix.reindex gridToColumn gridToColumn
      (NineRational.genericMatrix polynomialEmbedding) := by
  ext i q
  simp only [NineLinearObstruction.evaluationMatrix,
    NineField.coordinateTensorEmbedding_tmul, map_one, mul_one, one_mul,
    NineField.leftCoeff_augmented, NineField.rightCoeff_augmented]
  simp only [paramVector_eq_r, Matrix.reindex_apply, Matrix.submatrix_apply,
    NineRational.genericMatrix,
    polynomialEmbedding_T, polynomialEmbedding_U]
  rfl

theorem evaluationMatrix_det_ne_zero (t : Fin 9 → ℝ)
    (ht : AlgebraicIndependent ℚ t) :
    (NineLinearObstruction.evaluationMatrix (circleConfig t)
      (NineField.coordinateTensorEmbedding t ht) rowEquiv).det ≠ 0 := by
  rw [evaluationMatrix_eq, Matrix.det_reindex_self]
  exact NineRational.det_genericMatrix_ne_zero polynomialEmbedding
    polynomialEmbedding_injective

/-- Nine algebraically independent real parameters give a non-Ramsey configuration. -/
theorem nine_circle_not_ramsey (t : Fin 9 → ℝ)
    (ht : AlgebraicIndependent ℚ t) : ¬ Ramsey (circleConfig t) := by
  exact NineLinearObstruction.not_ramsey_of_det_ne_zero (circleConfig t)
    (by decide) (by decide) (circleConfig_affineSpan t ht)
    (NineField.coordinateTensorEmbedding t ht)
    (NineField.coordinateTensorEmbedding_injective t ht) rowEquiv
    (evaluationMatrix_det_ne_zero t ht)

/-- Nine distinct points on the unit circle form a non-Ramsey configuration. -/
theorem nine_circle_configuration (t : Fin 9 → ℝ)
    (ht : AlgebraicIndependent ℚ t) :
    Function.Injective (circleConfig t) ∧
      (∀ i, dist (circleConfig t i) 0 = 1) ∧ ¬ Ramsey (circleConfig t) :=
  ⟨circleConfig_injective t ht, circleConfig_on_circle t, nine_circle_not_ramsey t ht⟩

end EuclideanRamsey.NineMain

end

end OAI
end
end

section
section
namespace OAI

/-! The literal rational parametrization of the nine-point circle configuration. -/

noncomputable section
namespace EuclideanRamsey.NineStatement


theorem literalCircleConfig_eq (t : Fin 9 → ℝ) :
    literalCircleConfig t = NineGeometry.circleConfig t := by
  funext i
  ext j
  fin_cases j <;>
    simp [literalCircleConfig, NineGeometry.circleConfig]

/-- Nine points on the unit circle form a non-Ramsey configuration when their
parameters are algebraically independent over the rationals. -/
theorem nine_circle_configuration_oai (t : Fin 9 → ℝ)
    (ht : AlgebraicIndependent ℚ t) :
    Function.Injective (literalCircleConfig t) ∧
      (∀ i, dist (literalCircleConfig t i) 0 = 1) ∧
      ¬ Ramsey (literalCircleConfig t) := by
  rw [literalCircleConfig_eq]
  exact NineMain.nine_circle_configuration t ht

end EuclideanRamsey.NineStatement

end

end OAI
end
end

theorem solution : type_of% @OAI.EuclideanRamsey.NineStatement.nine_circle_configuration_oai := @OAI.EuclideanRamsey.NineStatement.nine_circle_configuration_oai
