-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_average_mem
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T19:21:18.740692+00:00
-- url     : https://prove2.me/submissions/53fb585a-ad20-4cf1-ab33-d7365f67d913

import Theorems.Thm_MasulloGRH_schwartz_correspondence
import Theorems.Thm_MasulloGRH_schwartzBruhat_exists_stages
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
import Theorems.Thm_MasulloGRH_quotient_goodSubgroup_dual_compactlyGenerated
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup

set_option autoImplicit false

universe u

namespace AvgMemAux

open MasulloGRH MeasureTheory

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]

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


lemma avg_eq_haar (k : Subgroup H) (hk : IsCompact (k : Set H)) (F : H → ℂ) (x : H) :
    letI : MeasurableSpace k := borel k
    haveI : BorelSpace k := ⟨rfl⟩
    haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
    schwartzBruhatAverage ⊤ k F x = ∫ y : k, F (x * y) ∂(Measure.haarMeasure ⊤) := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have h2 : subgroupHaar k = Measure.haarMeasure ⊤ := by
    unfold subgroupHaar
    rw [dif_pos hk]
  rw [h2]

lemma avg_subgroupOf [SecondCountableTopology H] (Ω k : Subgroup H) (hkΩ : k ≤ Ω)
    (hk : IsCompact (k : Set H)) (F : H → ℂ) (p : Ω) :
    schwartzBruhatAverage ⊤ (k.subgroupOf Ω) (fun x : Ω => F x) p =
      schwartzBruhatAverage ⊤ k F p := by
  have hk2 : IsCompact ((k.subgroupOf Ω : Subgroup Ω) : Set Ω) := by
    rw [Subtype.isCompact_iff]
    have : ((↑) : Ω → H) '' ((k.subgroupOf Ω : Subgroup Ω) : Set Ω) = (k : Set H) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hkΩ hx⟩, hx, rfl⟩
    rw [this]; exact hk
  haveI : SecondCountableTopology k := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology Ω := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (k.subgroupOf Ω) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  letI : MeasurableSpace (k.subgroupOf Ω) := borel _
  haveI : BorelSpace (k.subgroupOf Ω) := ⟨rfl⟩
  haveI : CompactSpace (k.subgroupOf Ω) := isCompact_iff_compactSpace.mp hk2
  rw [avg_eq_haar _ hk2, avg_eq_haar k hk]
  let e : (k.subgroupOf Ω) ≃* k := Subgroup.subgroupOfEquivOfLe hkΩ
  have hec : Continuous e := by
    show Continuous fun x : k.subgroupOf Ω => (⟨x.1.1, x.2⟩ : k)
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hsymm : Continuous e.symm :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  let E : (k.subgroupOf Ω) ≃ₜ k := ⟨e.toEquiv, hec, hsymm⟩
  haveI := MulEquiv.isHaarMeasure_map
    (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (k.subgroupOf Ω))) e hec hsymm
  have hmap : Measure.map e
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (k.subgroupOf Ω))) =
      Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k) := by
    rw [Measure.haarMeasure_unique (Measure.map e
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (k.subgroupOf Ω)))) ⊤]
    have h1 : (Measure.map e (Measure.haarMeasure
        (⊤ : TopologicalSpace.PositiveCompacts (k.subgroupOf Ω))))
        ((⊤ : TopologicalSpace.PositiveCompacts k) : Set k) = 1 := by
      rw [Measure.map_apply hec.measurable (by simp)]
      have := Measure.haarMeasure_self
        (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (k.subgroupOf Ω)))
      simpa using this
    rw [h1, one_smul]
  rw [← hmap]
  exact (E.measurableEmbedding.integral_map (fun y : k => F (↑p * ↑y))).symm


lemma avg_mul_left (k : Subgroup H) (w F : H → ℂ) (x : H)
    (hw : ∀ y ∈ k, w (x * y) = w x) :
    schwartzBruhatAverage ⊤ k (fun z => w z * F z) x = w x * schwartzBruhatAverage ⊤ k F x := by
  letI : MeasurableSpace k := borel k
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H)),
    Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have : (fun y : k => w (x * y) * F (x * y)) = fun y : k => w x * F (x * y) :=
    funext fun y => by rw [hw y y.2]
  simp only [this]
  exact integral_const_mul _ _

lemma avg_congr (k : Subgroup H) (F F' : H → ℂ) (x : H)
    (h : ∀ y ∈ k, F (x * y) = F' (x * y)) :
    schwartzBruhatAverage ⊤ k F x = schwartzBruhatAverage ⊤ k F' x := by
  letI : MeasurableSpace k := borel k
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H)),
    Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have : (fun y : k => F (x * y)) = fun y : k => F' (x * y) := funext fun y => h y y.2
  simp only [this]

end AvgMemAux

open MasulloGRH AvgMemAux Set Topology in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k : Subgroup G) (hk : IsGoodSubgroup k)
    (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) :
    schwartzBruhatAverage ⊤ k f ∈ schwartzBruhatSubmodule G := by
  classical
  haveI : IsClosed (k : Set G) := hk.1
  have hkc : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hk
  -- `f` lies in a single stage
  obtain ⟨ms, ns, rs, ss, ds, J, P, hd, -, -, -, hfix, hJ, -, -⟩ := schwartzBruhat_exists_stages G
  obtain ⟨N, hN⟩ := hfix ⟨f, hf⟩
  obtain ⟨Γ, k₁, π, hs, hπ, hJN⟩ := hJ N
  set g := P N ⟨f, hf⟩ with hg
  have hfΓ : f = extendPullback Γ π g.toFun := by
    have := congrArg Subtype.val (hN.symm.trans (hJN g))
    exact this
  -- the quotient
  let q : G →* G ⧸ k := QuotientGroup.mk' k
  have hqc : Continuous q := continuous_quot_mk
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  let Γ' : Subgroup (G ⧸ k) := Γ.map q
  let Ω : Subgroup G := Γ'.comap q
  have hΓΩ : Γ ≤ Ω := Subgroup.le_comap_map q Γ
  have hkΩ : k ≤ Ω := fun x hx => by
    show q x ∈ Γ'
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).2 hx]; exact Γ'.one_mem
  have hΓo : IsOpen (Γ : Set G) := hs.1
  have hΩo : IsOpen (Ω : Set G) := Subgroup.isOpen_mono hΓΩ hΓo
  have hΓ'o : IsOpen (Γ' : Set (G ⧸ k)) := by
    rw [Subgroup.coe_map]; exact hqo _ hΓo
  have hΓ'cg : IsCompactlyGeneratedSubgroup Γ' := by
    obtain ⟨U, hUc, hUΓ, ⟨V, hV, hVU⟩, hcl⟩ := hs.2.1
    refine ⟨q '' U, hUc.image hqc, ?_, ⟨q '' (V ∩ Γ), ?_, ?_⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hUΓ hx, rfl⟩
    · have := hqo.image_mem_nhds (Filter.inter_mem hV (hΓo.mem_nhds Γ.one_mem))
      rwa [map_one] at this
    · rintro _ ⟨⟨x, hx, rfl⟩, -⟩; exact ⟨x, hVU hx, rfl⟩
    · rw [← MonoidHom.map_closure, hcl]
  have hbot : IsGoodSubgroup (⊥ : Subgroup (G ⧸ k)) := by
    refine ⟨?_, ?_, ⊤, ?_, quotient_goodSubgroup_dual_compactlyGenerated G k hk⟩
    · show IsClosed ((⊥ : Subgroup (G ⧸ k)) : Set (G ⧸ k))
      rw [Subgroup.coe_bot]; exact isClosed_singleton
    · have : annihilator (⊥ : Subgroup (G ⧸ k)) = Set.univ := by
        ext χ; simp [annihilator]
      rw [this]; exact isOpen_univ
    · ext χ; simp [annihilator]
  have hs' : IsStructuralPair Γ' ⊥ := ⟨hΓ'o, hΓ'cg, hbot, bot_le⟩
  obtain ⟨m', n', r', s', d', π', hπ'⟩ := exists_elemPresentation_of_isStructuralPair (G ⧸ k) Γ' ⊥ hs'
  -- the groups for the correspondence
  haveI : LocallyCompactSpace Ω := hΩo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let P₀ : Subgroup Ω := Γ.subgroupOf Ω
  have hP₀ : IsOpen (P₀ : Set Ω) := by
    rw [Subgroup.coe_subgroupOf]; exact hΓo.preimage continuous_subtype_val
  let e := Subgroup.subgroupOfEquivOfLe hΓΩ
  have hec : Continuous e := by
    show Continuous fun x : P₀ => (⟨x.1.1, x.2⟩ : Γ)
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hsymm : Continuous e.symm :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  let E : P₀ ≃ₜ Γ := ⟨e.toEquiv, hec, hsymm⟩
  have heo : IsOpenMap e := E.isOpenMap
  let α : P₀ →* Multiplicative (ElemGroup (ms N) (ns N) (rs N) (ss N) (ds N)) :=
    π.comp e.toMonoidHom
  have hαc : Continuous α := hπ.2.1.comp hec
  have hαo : IsOpenMap α := hπ.2.2.1.comp heo
  have hαk : IsCompact {x : P₀ | α x = 1} := by
    have hK : IsCompact {y : Γ | π y = 1} := by
      rw [Subtype.isCompact_iff]
      have : ((↑) : Γ → G) '' {y : Γ | π y = 1} = (k₁ : Set G) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩; exact (hπ.2.2.2.2 y).1 hy
        · intro hx; exact ⟨⟨x, hs.2.2.2 hx⟩, (hπ.2.2.2.2 _).2 hx, rfl⟩
      rw [this]; exact isCompact_of_isGoodSubgroup G k₁ hs.2.2.1
    exact E.isCompact_preimage.2 hK
  let qΩ : Ω →* Γ' := (q.comp Ω.subtype).codRestrict Γ' (fun x => x.2)
  let β : Ω →* Multiplicative (ElemGroup m' n' r' s' d') := π'.comp qΩ
  have hqΩc : Continuous qΩ := (hqc.comp continuous_subtype_val).subtype_mk _
  have hβc : Continuous β := hπ'.2.1.comp hqΩc
  have hqΩo : IsOpenMap qΩ := by
    intro W hW
    obtain ⟨W₀, hW₀, rfl⟩ := isOpen_induced_iff.1 hW
    have : qΩ '' (((↑) : Ω → G) ⁻¹' W₀) = ((↑) : Γ' → G ⧸ k) ⁻¹' (q '' (W₀ ∩ Ω)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hzΩ⟩, hzy⟩
        exact ⟨⟨z, hzΩ⟩, hz, Subtype.ext hzy⟩
    rw [this]
    exact (hqo _ (hW₀.inter hΩo)).preimage continuous_subtype_val
  have hβo : IsOpenMap β := hπ'.2.2.1.comp hqΩo
  have hβker : ∀ x : Ω, β x = 1 ↔ (x : G) ∈ k := by
    intro x
    rw [show β x = π' (qΩ x) from rfl, hπ'.2.2.2.2, Subgroup.mem_bot]
    exact QuotientGroup.eq_one_iff _
  have hβk : IsCompact {x : Ω | β x = 1} := by
    rw [Subtype.isCompact_iff]
    have : ((↑) : Ω → G) '' {x : Ω | β x = 1} = (k : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact (hβker y).1 hy
      · intro hx; exact ⟨⟨x, hkΩ hx⟩, (hβker _).2 hx, rfl⟩
    rw [this]; exact hkc
  obtain ⟨T, -, hT⟩ := schwartz_correspondence Ω P₀ hP₀ (ms N) (ns N) (rs N) (ss N) (ds N) hπ.1
    α hαc hαo hαk m' n' r' s' d' β hβc hβo hβk
  have hext : ∀ x : Ω, extendPullback P₀ α g.toFun x = f x := by
    intro x
    rw [hfΓ]
    by_cases hx : (x : G) ∈ Γ
    · have hx' : x ∈ P₀ := hx
      unfold extendPullback
      rw [dif_pos hx', dif_pos hx]
      rfl
    · have hx' : x ∉ P₀ := hx
      unfold extendPullback
      rw [dif_neg hx', dif_neg hx]
  have hβker' : β.ker = k.subgroupOf Ω := by
    ext x; rw [MonoidHom.mem_ker, hβker]; rfl
  have havg : ∀ p : Ω, (T g).toFun (Multiplicative.toAdd (β p)) = schwartzBruhatAverage ⊤ k f p := by
    intro p
    rw [(hT g).1 p, hβker']
    have : extendPullback P₀ α g.toFun = fun x : Ω => f x := funext hext
    rw [this, avg_subgroupOf Ω k hkΩ hkc f p]
  have hΩeq : Ω = Γ ⊔ k := by
    show Subgroup.comap q (Subgroup.map q Γ) = Γ ⊔ k
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hΩcg : IsCompactlyGeneratedSubgroup Ω := by
    obtain ⟨U, hUc, hUΓ, ⟨V, hV, hVU⟩, hcl⟩ := hs.2.1
    refine ⟨U ∪ k, hUc.union hkc, Set.union_subset (hUΓ.trans hΓΩ) hkΩ,
      ⟨V ∩ Γ, Filter.inter_mem hV (hΓo.mem_nhds Γ.one_mem), ?_⟩, ?_⟩
    · rintro x ⟨⟨hxV, hxΓ⟩, -⟩; exact Or.inl (hVU ⟨hxV, hxΓ⟩)
    · rw [Subgroup.closure_union, hcl, Subgroup.closure_eq, hΩeq]
  have hβs : Function.Surjective β := by
    intro e'
    obtain ⟨y, rfl⟩ := hπ'.2.2.2.1 e'
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨x, hΓΩ hx⟩, by show π' (qΩ _) = π' y; congr 1; exact Subtype.ext hxy⟩
  have hs'' : IsStructuralPair Ω k := ⟨hΩo, hΩcg, hk, hkΩ⟩
  have hπ'' : IsElemPresentation Ω k β := ⟨hπ'.1, hβc, hβo, hβs, hβker⟩
  have hfun : schwartzBruhatAverage ⊤ k f = extendPullback Ω β (T g).toFun := by
    funext x
    by_cases hx : x ∈ Ω
    · unfold extendPullback
      rw [dif_pos hx, havg ⟨x, hx⟩]
    · unfold extendPullback
      rw [dif_neg hx]
      have h0 : schwartzBruhatAverage ⊤ k f x = schwartzBruhatAverage ⊤ k (fun z => (0 : ℂ) * f z) x := by
        refine avg_congr k _ _ x fun y hy => ?_
        rw [zero_mul, hfΓ]
        unfold extendPullback
        rw [dif_neg]
        intro hxy
        apply hx
        have := Ω.mul_mem (hΓΩ hxy) (Ω.inv_mem (hkΩ hy))
        simpa using this
      rw [h0, avg_mul_left k (fun _ => (0 : ℂ)) f x (fun _ _ => rfl), zero_mul]
  rw [hfun]
  exact Submodule.subset_span ⟨Ω, k, m', n', r', s', d', β, T g, hs'', hπ'', rfl⟩
