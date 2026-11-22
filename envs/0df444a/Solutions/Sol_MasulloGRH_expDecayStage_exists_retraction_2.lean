-- Prove2me | solution 2 for MasulloGRH.expDecayStage_exists_retraction
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T18:59:55.335087+00:00
-- url     : https://prove2.me/submissions/3bcfaeaf-29b5-4d60-a750-b0f5e16623c4

import Theorems.Thm_MasulloGRH_expDecayStage_concrete
import Theorems.Thm_MasulloGRH_schwartzBruhatAverage_transfer
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_isCompact_moduleKernel_and_compact_le
import Theorems.Thm_MasulloGRH_expDecaySchwartz_exists_good_invariant
import Theorems.Thm_MasulloGRH_elemSchwartz_frechet_nuclear_montel

set_option autoImplicit false

universe u

namespace MasulloGRHRetractAux


open MasulloGRH MeasureTheory

variable {H : Type u} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]

lemma extendPullback_top {m n r s : ℕ} {d : Fin s → ℕ}
    (π : (⊤ : Subgroup H) →* Multiplicative (ElemGroup m n r s d))
    (g : ElemGroup m n r s d → ℂ) (x : H) :
    extendPullback ⊤ π g x = g (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩)) := by
  unfold extendPullback
  rw [dif_pos (Subgroup.mem_top x)]

lemma pullback_mul {m n r s : ℕ} {d : Fin s → ℕ} (k : Subgroup H)
    (π : (⊤ : Subgroup H) →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation ⊤ k π) (g : ElemGroup m n r s d → ℂ) (x y : H) (hy : y ∈ k) :
    extendPullback ⊤ π g (x * y) = extendPullback ⊤ π g x := by
  rw [extendPullback_top, extendPullback_top]
  have h1 : π ⟨y, Subgroup.mem_top y⟩ = 1 := (hπ.2.2.2.2 ⟨y, Subgroup.mem_top y⟩).2 hy
  have : (⟨x * y, Subgroup.mem_top _⟩ : (⊤ : Subgroup H)) =
      ⟨x, Subgroup.mem_top x⟩ * ⟨y, Subgroup.mem_top y⟩ := rfl
  rw [this, map_mul, h1, mul_one]

lemma average_eq (k₀ : Subgroup H) (hk₀ : IsCompact (k₀ : Set H)) (f : H → ℂ)
    (hf : ∀ x, ∀ y ∈ k₀, f (x * y) = f x) (x : H) :
    schwartzBruhatAverage ⊤ k₀ f x = f x := by
  letI : MeasurableSpace k₀ := borel k₀
  haveI : BorelSpace k₀ := ⟨rfl⟩
  haveI : CompactSpace k₀ := isCompact_iff_compactSpace.mp hk₀
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have h1 : (fun y : k₀ => f (x * y)) = fun _ => f x := funext fun y => hf x y y.2
  have h2 : subgroupHaar k₀ = Measure.haarMeasure ⊤ := by
    unfold subgroupHaar
    rw [dif_pos hk₀]
  simp only [h1, h2, integral_const]
  have h3 : (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k₀)) Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts k₀))
    simpa using this
  simp [measureReal_def, h3]

lemma es_ext {m n r s : ℕ} {d : Fin s → ℕ} {f g : ElemSchwartz m n r s d}
    (h : ∀ z, f.toFun z = g.toFun z) : f = g :=
  Subtype.ext (funext h)

lemma cont_of_top_eq {α β : Type*} [TopologicalSpace α] {tβ t' : TopologicalSpace β}
    (h : tβ = t') {f : α → β} (hf : @Continuous α β _ t' f) : @Continuous α β _ tβ f := by
  rw [h]; exact hf

lemma cont_dom_of_top_eq {α β : Type*} {tα t' : TopologicalSpace α} [TopologicalSpace β]
    (h : tα = t') {f : α → β} (hf : @Continuous α β t' _ f) : @Continuous α β tα _ f := by
  rw [h]; exact hf


/-- the kernel of a module as a subgroup -/
def modKer {m : H → ℝ} (hm : IsModule m) : Subgroup H where
  carrier := {g | m g = 1}
  one_mem' := by
    show m 1 = 1
    have h := hm.map_mul 1 1
    rw [mul_one] at h
    have hp := hm.pos 1
    nlinarith
  mul_mem' {a b} ha hb := by
    show m (a * b) = 1
    rw [hm.map_mul, show m a = 1 from ha, show m b = 1 from hb, one_mul]
  inv_mem' {a} ha := by
    show m a⁻¹ = 1
    have h := hm.map_mul a a⁻¹
    rw [mul_inv_cancel, show m a = 1 from ha, one_mul] at h
    have h1 := hm.map_mul 1 1
    rw [mul_one] at h1
    have hp := hm.pos 1
    have : m 1 = 1 := by nlinarith
    rw [← h, this]

lemma module_mul_of_compact {m : H → ℝ} (hm : IsRposModule m) (k : Subgroup H)
    (hk : IsCompact (k : Set H)) (x y : H) (hy : y ∈ k) : m (x * y) = m x := by
  have h := (isCompact_moduleKernel_and_compact_le H m hm (modKer hm.1) (fun _ => Iff.rfl)).2 k hk hy
  rw [hm.1.map_mul, show m y = 1 from h, mul_one]

lemma average_weight {m : H → ℝ} (hm : IsRposModule m) (k : Subgroup H)
    (hk : IsCompact (k : Set H)) (a : ℝ) (f : H → ℂ) (x : H) :
    schwartzBruhatAverage ⊤ k (fun x => ((m x ^ a : ℝ) : ℂ) * f x) x =
      ((m x ^ a : ℝ) : ℂ) * schwartzBruhatAverage ⊤ k f x := by
  letI : MeasurableSpace k := borel k
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H)),
    Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have h1 : (fun y : k => ((m (x * y) ^ a : ℝ) : ℂ) * f (x * y)) =
      fun y : k => ((m x ^ a : ℝ) : ℂ) * f (x * y) :=
    funext fun y => by rw [module_mul_of_compact hm k hk x y y.2]
  simp only [h1]
  exact integral_const_mul _ _

lemma average_add (k : Subgroup H) (hk : IsCompact (k : Set H)) (f g : H → ℂ)
    (hf : Continuous f) (hg : Continuous g) (x : H) :
    schwartzBruhatAverage ⊤ k (f + g) x =
      schwartzBruhatAverage ⊤ k f x + schwartzBruhatAverage ⊤ k g x := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  unfold schwartzBruhatAverage
  simp only [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have h2 : subgroupHaar k = Measure.haarMeasure ⊤ := by
    unfold subgroupHaar
    rw [dif_pos hk]
  rw [h2]
  have hi : ∀ f : H → ℂ, Continuous f → Integrable (fun y : k => f (x * y))
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k)) := fun f hf =>
    (hf.comp (continuous_const.mul continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact integral_add (hi f hf) (hi g hg)

lemma average_smul (k : Subgroup H) (c : ℂ) (f : H → ℂ) (x : H) :
    schwartzBruhatAverage ⊤ k (fun x => c * f x) x = c * schwartzBruhatAverage ⊤ k f x := by
  letI : MeasurableSpace k := borel k
  unfold schwartzBruhatAverage
  simp only [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  exact integral_const_mul _ _

lemma expDecay_continuous {m : H → ℝ} {I : Set ℝ} (ϕ : ExpDecaySchwartz H m I) :
    Continuous ϕ.toFun := by
  have : ∀ f ∈ expDecaySubmodule H m I, Continuous f := by
    intro f hf
    refine Submodule.span_induction (p := fun f _ => Continuous f) ?_ ?_ ?_ ?_ hf
    · exact fun f hf => hf.1
    · exact continuous_const
    · exact fun f g _ _ hf hg => hf.add hg
    · exact fun c f _ hf => continuous_const.mul hf
  exact this _ ϕ.2

lemma ws_all {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) :
    WithSeminorms (fun q : {q : Seminorm ℂ E // Continuous q} => q.1) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm (le_iInf fun q => ?_) ?_
  · rw [← Filter.tendsto_iff_comap]
    have := q.2.tendsto 0
    rwa [map_zero] at this
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf p).1 hp]
    exact le_iInf fun i => iInf_le_of_le ⟨p i, hp.continuous_seminorm i⟩ le_rfl

/-- a projective topology of linear maps into a locally convex space is locally convex -/
lemma lc_iInf_induced {E : Type u} [AddCommGroup E] [Module ℂ E]
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    {κ : Type*} {q : SeminormFamily ℂ F κ} (hq : WithSeminorms q)
    {ι : Type*} [Nonempty ι] [Nonempty κ] (L : ι → E →ₗ[ℂ] F) :
    IsLocallyConvexTopology E (⨅ i, TopologicalSpace.induced (L i) inferInstance) := by
  have hws := withSeminorms_iInf (fun i => LinearMap.withSeminorms_induced hq (L i))
  letI : TopologicalSpace E := ⨅ i, TopologicalSpace.induced (L i) inferInstance
  haveI : IsTopologicalAddGroup E := hws.topologicalAddGroup
  exact ⟨{q : Seminorm ℂ E // Continuous q}, ⟨⟨0, continuous_const⟩⟩, _, ws_all hws⟩

end MasulloGRHRetractAux

open MasulloGRH MasulloGRHRetractAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k) :
    ∃ P : ExpDecaySchwartz G m I →ₗ[ℂ] ExpDecayStage G m I k, Continuous P ∧
      ∀ y, P (ExpDecayStage.incl G m I k y) = y := by
  obtain ⟨a₀, ha₀⟩ := hne
  have hne : I.Nonempty := ⟨a₀, ha₀⟩
  obtain ⟨hs, -, hW⟩ := expDecayStage_concrete G m hm I hne k hk
  obtain ⟨m₁, n₁, r₁, s₁, d₁, π, hπ⟩ := exists_elemPresentation_of_isStructuralPair G ⊤ k hs
  obtain ⟨W, hWa, hWtop, hWsurj⟩ := hW m₁ n₁ r₁ s₁ d₁ π hπ
  have hkc : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hk
  have hmpos : ∀ (x : G) (a : ℝ), ((m x ^ a : ℝ) : ℂ) ≠ 0 := fun x a =>
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (hm.1.pos x) a).ne'
  -- the averaged weighted functions of a stage `k''`, as continuous maps into `S(G/k)`
  have key : ∀ k'' : Subgroup G, IsGoodSubgroup k'' → ∀ a ∈ I,
      ∃ F : ExpDecayStage G m I k'' → ElemSchwartz m₁ n₁ r₁ s₁ d₁, Continuous F ∧
        ∀ (ϕ : ExpDecayStage G m I k'') (x : G),
          (F ϕ).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩)) =
            ((m x ^ a : ℝ) : ℂ) * schwartzBruhatAverage ⊤ k ϕ.1.toFun x := by
    intro k'' hk'' a ha
    obtain ⟨hs'', -, hW''⟩ := expDecayStage_concrete G m hm I hne k'' hk''
    obtain ⟨m₂, n₂, r₂, s₂, d₂, π'', hπ''⟩ :=
      exists_elemPresentation_of_isStructuralPair G ⊤ k'' hs''
    obtain ⟨W'', hWa'', hWtop'', -⟩ := hW'' m₂ n₂ r₂ s₂ d₂ π'' hπ''
    obtain ⟨T, hTc, hT⟩ := schwartzBruhatAverage_transfer G ⊤ k'' m₂ n₂ r₂ s₂ d₂ π'' hs'' hπ''
      ⊤ k m₁ n₁ r₁ s₁ d₁ π hs hπ
    have hWc : Continuous (W'' a) :=
      cont_dom_of_top_eq hWtop'' (continuous_iInf_dom (continuous_iInf_dom (i := ha)
        continuous_induced_dom))
    refine ⟨T ∘ W'' a, hTc.comp hWc, fun ϕ x => ?_⟩
    have h1 := congrFun (hT (W'' a ϕ)) x
    rw [extendPullback_top] at h1
    show (T (W'' a ϕ)).toFun _ = _
    rw [← h1, ← average_weight hm k hkc a ϕ.1.toFun x]
    congr 1
    funext y
    rw [extendPullback_top, hWa'' a ha ϕ y]
    rfl
  -- the average of an element of `S_I(G)` lies in the stage
  have hex : ∀ ϕ : ExpDecaySchwartz G m I, ∃ ψ : ExpDecayStage G m I k,
      ψ.1.toFun = schwartzBruhatAverage ⊤ k ϕ.toFun := by
    intro ϕ
    obtain ⟨k'', hk'', hϕ⟩ := expDecaySchwartz_exists_good_invariant G m hm I hI hne ϕ
    choose F _ hF using key k'' hk''
    classical
    let g : ℝ → ElemSchwartz m₁ n₁ r₁ s₁ d₁ := fun a => if ha : a ∈ I then F a ha ⟨ϕ, hϕ⟩ else 0
    have hg : ∀ a (ha : a ∈ I) (x : G),
        (g a).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩)) =
          ((m x ^ a : ℝ) : ℂ) * schwartzBruhatAverage ⊤ k ϕ.toFun x := by
      intro a ha x
      simp only [g, dif_pos ha]
      exact hF a ha ⟨ϕ, hϕ⟩ x
    obtain ⟨ψ, hψ⟩ := hWsurj g (fun a ha b hb x => by
      rw [hg a ha, hg b hb, ← mul_assoc, ← Complex.ofReal_mul,
        ← Real.rpow_add (hm.1.pos x), sub_add_cancel])
    refine ⟨ψ, funext fun x => ?_⟩
    have h1 := hWa a₀ ha₀ ψ x
    rw [hψ a₀ ha₀, hg a₀ ha₀] at h1
    exact (mul_left_cancel₀ (hmpos x a₀) h1).symm
  choose P₀ hP₀ using hex
  have hinj : ∀ ψ ψ' : ExpDecayStage G m I k, ψ.1.toFun = ψ'.1.toFun → ψ = ψ' :=
    fun ψ ψ' h => Subtype.ext (Subtype.ext h)
  let P : ExpDecaySchwartz G m I →ₗ[ℂ] ExpDecayStage G m I k :=
    { toFun := P₀
      map_add' := fun ϕ ψ => by
        apply hinj
        show (P₀ (ϕ + ψ)).1.toFun = (P₀ ϕ).1.toFun + (P₀ ψ).1.toFun
        rw [hP₀, hP₀, hP₀]
        funext x
        exact average_add k hkc _ _ (expDecay_continuous ϕ) (expDecay_continuous ψ) x
      map_smul' := fun c ϕ => by
        apply hinj
        show (P₀ (c • ϕ)).1.toFun = fun x => c * (P₀ ϕ).1.toFun x
        rw [hP₀, hP₀]
        funext x
        exact average_smul k c _ x }
  have hP : ∀ ϕ, (P ϕ).1.toFun = schwartzBruhatAverage ⊤ k ϕ.toFun := hP₀
  refine ⟨P, ?_, fun y => ?_⟩
  · -- continuity through the universal property of the inductive topology
    obtain ⟨⟨ι, _, q, hq⟩, -, -⟩ := (elemSchwartz_frechet_nuclear_montel m₁ n₁ r₁ s₁ d₁ hπ.1).1
    haveI : Nonempty I := ⟨⟨a₀, ha₀⟩⟩
    have hlc := lc_iInf_induced (E := ExpDecaySchwartz G m I) hq
      (fun a : I => (W a).comp P)
    have hτ : TopologicalSpace.induced P (inferInstance : TopologicalSpace (ExpDecayStage G m I k)) =
        ⨅ a : I, TopologicalSpace.induced ((W a).comp P) inferInstance := by
      rw [hWtop]
      simp only [induced_iInf, induced_compose]
      rw [iInf_subtype']
      rfl
    rw [continuous_iff_le_induced, hτ]
    refine sInf_le ⟨hlc, fun k'' hk'' => ?_⟩
    refine continuous_iInf_rng.2 fun a => continuous_induced_rng.2 ?_
    obtain ⟨F, hFc, hF⟩ := key k'' hk'' a a.2
    have e : (fun ϕ : ExpDecayStage G m I k'' => W a (P ϕ.1)) = F := by
      funext ϕ
      refine es_ext fun z => ?_
      obtain ⟨x, hx⟩ := hπ.2.2.2.1 (Multiplicative.ofAdd z)
      have hz : z = Multiplicative.toAdd (π ⟨(x : G), Subgroup.mem_top _⟩) := by
        rw [Subtype.coe_eta, hx]; rfl
      show (W a (P ϕ.1)).toFun z = (F ϕ).toFun z
      rw [hz, hF ϕ x, hWa a a.2 (P ϕ.1) x]
      congr 1
      exact congrFun (hP ϕ.1) x
    show @Continuous (ExpDecayStage G m I k'') _ inferInstance _
      (fun ϕ : ExpDecayStage G m I k'' => W a (P ϕ.1))
    rw [e]
    exact hFc
  · apply hinj
    rw [hP]
    funext x
    exact average_eq k hkc _ (fun x h hh => y.2 h hh x) x
