-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b85eea77-7b0d-56ee-9e46-147cc0f2e89f

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_map_eq_natCard_smul_of_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory NumberField P2MW.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower.NumberField IsDedekindDomain"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower.NumberField.PlaceDecomp"

namespace NumberField
p2m_export "NumberField" "mk place PlaceDecomp.decomp PlaceDecomp.actRingEquiv_apply PlaceDecomp.smul_def PlaceDecomp.coe_smul_units PlaceDecomp.exists_restrict_decomp_surjective_of_tower PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp actRingEquiv_apply smul_def coe_smul_units exists_restrict_decomp_surjective_of_tower forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace InfFundProof
p2m_open "NumberField.PlaceDecomp NumberField"

open ExtCitation.LocalLevel

theorem map_eq_map_of_hom_eq {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) (φ₁ : Rep.res f₁ A ⟶ B) (φ₂ : Rep.res f₂ A ⟶ B)
    (hφ : ∀ a : A, φ₁.hom a = φ₂.hom a) (n : ℕ) :
    groupCohomology.map f₁ φ₁ n = groupCohomology.map f₂ φ₂ n := by
  subst h
  obtain rfl : φ₁ = φ₂ := by
    ext a
    exact hφ a
  rfl

noncomputable def resRepHom {G H : Type} [Group G] [Group H] (φ : H →* G) {M N : Type} [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction H N] (f : M →* N) (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    Rep.res φ (Rep.ofMulDistribMulAction G M) ⟶ Rep.ofMulDistribMulAction H N :=
  Rep.ofHom ⟨(MonoidHom.toAdditive f).toIntLinearMap, fun h => LinearMap.ext fun a => by
    change Additive.ofMul (f (φ h • (Additive.toMul : _ ≃ M) a)) = Additive.ofMul (h • f ((Additive.toMul : _ ≃ M) a))
    rw [hf]⟩

theorem resRepHom_apply {G H : Type} [Group G] [Group H] (φ : H →* G) {M N : Type} [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction H N] (f : M →* N) (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (m : M) :
    (resRepHom φ f hf).hom (Additive.ofMul m) = Additive.ofMul (f m) := rfl

noncomputable def thetaOf {G : Type} [Group G] {Kw : Type} [Field Kw] [MulSemiringAction G Kw]
    {q : ℕ} [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [MulSemiringAction G L'] [MulDistribMulAction G (↥L')ˣ]
    [MulDistribMulAction G Kwˣ] (hcKw : ∀ (g : G) (u : Kwˣ), ((g • u : Kwˣ) : Kw) = g • (u : Kw))
    (Φ : Kw ≃+* L') (hc : ∀ (g : G) (u : (↥L')ˣ), ((g • u : (↥L')ˣ) : L') = g • (u : L'))
    (hΦ : ∀ (g : G) (y : Kw), Φ (g • y) = g • Φ y) :
    Rep.ofMulDistribMulAction G (↥L')ˣ ⟶ Rep.ofMulDistribMulAction G Kwˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map Φ.symm.toRingHom.toMonoidHom)).toIntLinearMap, fun g => LinearMap.ext fun a => by
    change Additive.ofMul (Units.map Φ.symm.toRingHom.toMonoidHom (g • (Additive.toMul : _ ≃ (↥L')ˣ) a))
      = Additive.ofMul (g • Units.map Φ.symm.toRingHom.toMonoidHom ((Additive.toMul : _ ≃ (↥L')ˣ) a))
    congr 1
    apply Units.ext
    rw [hcKw, Units.coe_map, Units.coe_map, hc]
    change Φ.symm (g • _) = g • Φ.symm _
    apply Φ.injective
    rw [hΦ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]⟩

theorem thetaOf_apply {G : Type} [Group G] {Kw : Type} [Field Kw] [MulSemiringAction G Kw]
    {q : ℕ} [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [MulSemiringAction G L'] [MulDistribMulAction G (↥L')ˣ]
    [MulDistribMulAction G Kwˣ] (hcKw : ∀ (g : G) (u : Kwˣ), ((g • u : Kwˣ) : Kw) = g • (u : Kw))
    (Φ : Kw ≃+* L') (hc : ∀ (g : G) (u : (↥L')ˣ), ((g • u : (↥L')ˣ) : L') = g • (u : L'))
    (hΦ : ∀ (g : G) (y : Kw), Φ (g • y) = g • Φ y) (y : (↥L')ˣ) :
    ((Additive.toMul ((thetaOf L' hcKw Φ hc hΦ).hom (Additive.ofMul y)) : Kwˣ) : Kw) = Φ.symm (y : L') := rfl

noncomputable def fixedBase {G : Type} [Group G] {q : ℕ} [Fact q.Prime] (L'' : IntermediateField ℚ_[q] (PadicAlgCl q))
    [MulSemiringAction G L''] (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L'' x = algebraMap ℚ_[q] L'' x) :
    IntermediateField ℚ_[q] (PadicAlgCl q) :=
  ((FixedPoints.subfield G (↥L'')).map (L''.val : ↥L'' →+* PadicAlgCl q)).toIntermediateField fun a =>
    ⟨algebraMap ℚ_[q] L'' a, fun g => hG g a, rfl⟩

theorem mem_fixedBase_iff {G : Type} [Group G] {q : ℕ} [Fact q.Prime] (L'' : IntermediateField ℚ_[q] (PadicAlgCl q))
    [MulSemiringAction G L''] (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L'' x = algebraMap ℚ_[q] L'' x)
    (x : PadicAlgCl q) : x ∈ fixedBase L'' hG ↔ ∃ y : ↥L'', (∀ g : G, g • y = y) ∧ (y : PadicAlgCl q) = x := by
  change x ∈ ((FixedPoints.subfield G (↥L'')).map (L''.val : ↥L'' →+* PadicAlgCl q)) ↔ _
  rw [Subfield.mem_map]
  rfl

theorem coe_mem_fixedBase_iff {G : Type} [Group G] {q : ℕ} [Fact q.Prime] (L'' : IntermediateField ℚ_[q] (PadicAlgCl q))
    [MulSemiringAction G L''] (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L'' x = algebraMap ℚ_[q] L'' x)
    (y : ↥L'') : (y : PadicAlgCl q) ∈ fixedBase L'' hG ↔ ∀ g : G, g • y = y := by
  rw [mem_fixedBase_iff]
  constructor
  · rintro ⟨y', hy', h⟩
    obtain rfl : y' = y := Subtype.ext h
    exact hy'
  · exact fun h => ⟨y, h, rfl⟩

theorem fixedBase_le {G : Type} [Group G] {q : ℕ} [Fact q.Prime] (L'' : IntermediateField ℚ_[q] (PadicAlgCl q))
    [MulSemiringAction G L''] (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L'' x = algebraMap ℚ_[q] L'' x) :
    fixedBase L'' hG ≤ L'' := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (mem_fixedBase_iff L'' hG x).1 hx
  exact y.2

end NumberField.PlaceDecomp.InfFundProof

open _root_.NumberField.PlaceDecomp _root_.P2MW.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower.NumberField.PlaceDecomp NumberField.PlaceDecomp.InfFundProof ExtCitation.LocalLevel in
set_option maxHeartbeats 3200000 in

theorem solution
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
    (W : HeightOneSpectrum (𝓞 M))
    (hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E M W))
    (hsolv₁ : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))

    (r : ↥(NumberField.PlaceDecomp.decomp E M W) →* ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
    (hr : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E M W)) (x : F),
      algebraMap F M (((r σ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) x) = (σ : M ≃ₐ[E] M) (algebraMap F M x))
    (iD : Rep.res r (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (hiD : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ,
      ((Additive.toMul (iD.hom (Additive.ofMul x)) : (W.adicCompletion M)ˣ) : W.adicCompletion M) =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom F M (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M)) (x : (W.under (𝓞 F)).adicCompletion F))

    (q : ℕ) [Fact q.Prime] (L L'' : IntermediateField ℚ_[q] (PadicAlgCl q)) (hLL'' : L ≤ L'')
    [FiniteDimensional ℚ_[q] L] [FiniteDimensional ℚ_[q] L'']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) L]
    [FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) L]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L)ˣ]
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E M W)) L''] [FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E M W)) L'']
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥L'')ˣ]
    (Φ : (W.under (𝓞 F)).adicCompletion F ≃+* L) (Φ'' : W.adicCompletion M ≃+* L'')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (x : (W.under (𝓞 F)).adicCompletion F), Φ (g • x) = g • Φ x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (x : W.adicCompletion M), Φ'' (g • x) = g • Φ'' x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L'' x = algebraMap ℚ_[q] L'' x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (u : (↥L'')ˣ), ((g • u : (↥L'')ˣ) : L'') = g • (u : L''))
    (_ : ∀ x : (W.under (𝓞 F)).adicCompletion F,
      ((Φ'' (HeightOneSpectrum.Extension.adicCompletionSemialgHom F M
          (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M)) x) : L'') : PadicAlgCl q) = ((Φ x : L) : PadicAlgCl q)) :
    ∃ (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K₀)
      (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L)ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)
      (θ'' : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥L'')ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
      (u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L)ˣ))
      (u'' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥L'')ˣ)),
      ExtCitation.LocalLevel.IsBase q L (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) K₀ ∧
      ExtCitation.LocalLevel.IsBase q L'' (↥(NumberField.PlaceDecomp.decomp E M W)) K₀ ∧
      (∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : ((W.under (𝓞 F)).adicCompletion F)ˣ) : (W.under (𝓞 F)).adicCompletion F) = Φ.symm (y : L)) ∧
      (∀ y : (↥L'')ˣ, ((Additive.toMul (θ''.hom (Additive.ofMul y)) : (W.adicCompletion M)ˣ) : W.adicCompletion M) = Φ''.symm (y : L'')) ∧
      ExtCitation.LocalLevel.IsLocalFundamentalClass q L (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) K₀ u ∧
      ExtCitation.LocalLevel.IsLocalFundamentalClass q L'' (↥(NumberField.PlaceDecomp.decomp E M W)) K₀ u'' ∧
      (groupCohomology.map r iD 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) θ 2).hom u) =
        Nat.card ↥r.ker • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M W)) θ'' 2).hom u'' ∧
      Nat.card ↥(NumberField.PlaceDecomp.decomp E M W) = Nat.card ↥r.ker * Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) := by
  rename_i _ _ _ _ _ _ _ _ _ hΦ hΦ'' hqG hqG'' hc hc'' hcompat
  let i := HeightOneSpectrum.Extension.adicCompletionSemialgHom F M (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M))

  obtain ⟨r', hr'surj, hr'res, hr'ker, hr'lift, hr'semi⟩ := NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E F M W
  have hrr' : r = r' := by
    refine MonoidHom.ext fun σ => Subtype.ext (AlgEquiv.ext fun x => ?_)
    apply (algebraMap F M).injective
    rw [hr, hr'res]
    exact (AlgEquiv.restrictNormal_commutes (σ : M ≃ₐ[E] M) F x).symm
  subst hrr'
  have hsurj : Function.Surjective r := hr'surj
  have hsemi : ∀ (σ : ↥(decomp E M W)) (x : (W.under (𝓞 F)).adicCompletion F), i (r σ • x) = σ • i x := hr'semi

  have hact : ∀ (σ : ↥(decomp E M W)) (τ : ↥(decomp F M W)),
      (σ : M ≃ₐ[E] M) = AlgEquiv.restrictScalars E (τ : M ≃ₐ[F] M) → ∀ b : W.adicCompletion M, σ • b = τ • b := by
    intro σ τ hστ b
    rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def]
    apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
    rw [NumberField.PlaceDecomp.actRingEquiv_apply, NumberField.PlaceDecomp.actRingEquiv_apply, hστ]
    rfl

  have hcompat' : ∀ x : (W.under (𝓞 F)).adicCompletion F, Φ'' (i x) = IntermediateField.inclusion hLL'' (Φ x) := by
    intro x
    apply Subtype.ext
    rw [IntermediateField.coe_inclusion]
    exact hcompat x

  have he0 : ∀ (h : ↥(decomp E M W)) (x : ↥L),
      h • IntermediateField.inclusion hLL'' x = IntermediateField.inclusion hLL'' (r h • x) := by
    intro h x
    obtain ⟨a, rfl⟩ : ∃ a, Φ a = x := ⟨Φ.symm x, Φ.apply_symm_apply x⟩
    rw [← hcompat', ← hΦ'', ← hsemi, hcompat', hΦ]

  let K₀ := fixedBase L'' hqG''
  have hK₀L'' : K₀ ≤ L'' := fixedBase_le L'' hqG''
  haveI hfdK₀ : FiniteDimensional ℚ_[q] ↥K₀ :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hK₀L'').toLinearMap
      (fun a b h => Subtype.ext (by simpa [IntermediateField.coe_inclusion] using congrArg Subtype.val h))
  have hBase'' : IsBase q L'' (↥(decomp E M W)) K₀ :=
    ⟨hK₀L'', fun x => coe_mem_fixedBase_iff L'' hqG'' x⟩

  have hL : ∀ x : ↥L'', (x : PadicAlgCl q) ∈ L ↔ ∀ n ∈ r.ker, n • x = x := by
    intro x
    constructor
    · rintro hx n hn
      have hx' : x = IntermediateField.inclusion hLL'' ⟨x, hx⟩ := Subtype.ext (by rw [IntermediateField.coe_inclusion])
      rw [hx', he0, MonoidHom.mem_ker.1 hn, one_smul]
    · intro hfix

      haveI : IsGalois F M := IsGalois.tower_top_of_isGalois E F M
      have hb : ∀ τ : ↥(decomp F M W), τ • Φ''.symm x = Φ''.symm x := by
        intro τ
        obtain ⟨σ, hστ, hσ⟩ := hr'lift τ
        rw [← hact σ τ hστ]
        apply Φ''.injective
        rw [hΦ'', RingEquiv.apply_symm_apply]
        exact hfix σ (MonoidHom.mem_ker.2 hσ)
      obtain ⟨a, ha⟩ := (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom F M W (Φ''.symm x)).1 hb
      have hxa : x = Φ'' (i a) := by rw [ha, RingEquiv.apply_symm_apply]
      rw [hxa, hcompat', IntermediateField.coe_inclusion]
      exact (Φ a).2

  have hBase : IsBase q L (↥(decomp E F (W.under (𝓞 F)))) K₀ := by
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := (mem_fixedBase_iff L'' hqG'' x).1 hx
      exact (hL y).2 fun n _ => hy n
    · have hxx : ((x : PadicAlgCl q)) = ((IntermediateField.inclusion hLL'' x : ↥L'') : PadicAlgCl q) :=
        (IntermediateField.coe_inclusion hLL'' x).symm
      rw [hxx, coe_mem_fixedBase_iff]
      constructor
      · intro hfix g
        obtain ⟨h, rfl⟩ := hsurj g
        have := hfix h
        rw [he0] at this
        exact IntermediateField.inclusion_injective hLL'' this
      · intro hfix h
        rw [he0, hfix]

  let θ := thetaOf (G := ↥(decomp E F (W.under (𝓞 F)))) L (fun g u => NumberField.PlaceDecomp.coe_smul_units g u) Φ hc hΦ
  let θ'' := thetaOf (G := ↥(decomp E M W)) L'' (fun g u => NumberField.PlaceDecomp.coe_smul_units g u) Φ'' hc'' hΦ''
  obtain ⟨u, hu, -⟩ := ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q L (↥(decomp E F (W.under (𝓞 F)))) hqG hc hsolv₁ K₀ hBase
  obtain ⟨u'', hu'', -⟩ := ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q L'' (↥(decomp E M W)) hqG'' hc'' hsolv K₀ hBase''

  let eKer : (↥(decomp E M W) ⧸ r.ker) ≃* ↥(decomp E F (W.under (𝓞 F))) :=
    MulEquiv.ofBijective (QuotientGroup.kerLift r) ⟨QuotientGroup.kerLift_injective r, fun g => by
      obtain ⟨h, rfl⟩ := hsurj g
      exact ⟨QuotientGroup.mk h, QuotientGroup.kerLift_mk r h⟩⟩
  let e : ↥(decomp E F (W.under (𝓞 F))) ≃* ↥(decomp E M W) ⧸ r.ker := eKer.symm
  have he_symm : ∀ h : ↥(decomp E M W), e.symm (QuotientGroup.mk h) = r h := fun h => QuotientGroup.kerLift_mk r h
  have hcomp : e.symm.toMonoidHom.comp (QuotientGroup.mk' r.ker) = r := MonoidHom.ext fun h => he_symm h
  have he : ∀ (g : ↥(decomp E F (W.under (𝓞 F)))) (h : ↥(decomp E M W)), (QuotientGroup.mk h : ↥(decomp E M W) ⧸ r.ker) = e g →
      ∀ x : ↥L, ((g • x : ↥L) : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hLL'' x.2⟩ : ↥L'') : ↥L'') : PadicAlgCl q) := by
    intro g h hgh x
    have hg : r h = g := by rw [← he_symm, hgh, MulEquiv.symm_apply_apply]
    have hx : (⟨(x : PadicAlgCl q), hLL'' x.2⟩ : ↥L'') = IntermediateField.inclusion hLL'' x := rfl
    rw [hx, he0, IntermediateField.coe_inclusion, hg]
  have hιf : ∀ (h : ↥(decomp E M W)) (v : (↥L)ˣ),
      Units.map (IntermediateField.inclusion hLL'' : ↥L →* ↥L'') ((e.symm.toMonoidHom.comp (QuotientGroup.mk' r.ker)) h • v) =
        h • Units.map (IntermediateField.inclusion hLL'' : ↥L →* ↥L'') v := by
    intro h v
    apply Units.ext
    rw [hc'', Units.coe_map, Units.coe_map, hc, MonoidHom.coe_coe]
    change IntermediateField.inclusion hLL'' (e.symm (QuotientGroup.mk h) • (v : ↥L)) = _
    rw [he_symm, he0]
  let ι := resRepHom (e.symm.toMonoidHom.comp (QuotientGroup.mk' r.ker)) (Units.map (IntermediateField.inclusion hLL'' : ↥L →* ↥L'')) hιf
  have hι : ∀ v : (↥L)ˣ, (((Additive.toMul (ι.hom (Additive.ofMul v)) : (↥L'')ˣ) : ↥L'') : PadicAlgCl q) = ((v : ↥L) : PadicAlgCl q) :=
    fun v => IntermediateField.coe_inclusion hLL'' _

  have H := ExtCitation.LocalLevel.map_eq_natCard_smul_of_isLocalFundamentalClass q L'' (↥(decomp E M W)) hqG'' hc'' hsolv K₀ hBase''
    L hLL'' (↥(decomp E F (W.under (𝓞 F)))) hc r.ker e hL he u hu u'' hu'' ι hι

  refine ⟨K₀, hfdK₀, θ, θ'', u, u'', hBase, hBase'', fun y => rfl, fun y => rfl, hu, hu'', ?_, ?_⟩
  · have h1 := congrArg (fun T => T.hom u)
      (groupCohomology.map_comp (MonoidHom.id ↥(decomp E F (W.under (𝓞 F)))) r θ iD 2)
    have h2 := congrArg (fun T => T.hom u)
      (groupCohomology.map_comp (e.symm.toMonoidHom.comp (QuotientGroup.mk' r.ker)) (MonoidHom.id ↥(decomp E M W)) ι θ'' 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
    rw [← h1]
    have hgrp : (MonoidHom.id ↥(decomp E F (W.under (𝓞 F)))).comp r = (e.symm.toMonoidHom.comp (QuotientGroup.mk' r.ker)).comp (MonoidHom.id _) := by
      rw [MonoidHom.id_comp, MonoidHom.comp_id, hcomp]
    have key : groupCohomology.map ((MonoidHom.id ↥(decomp E F (W.under (𝓞 F)))).comp r) ((Rep.resFunctor r).map θ ≫ iD) 2 =
        groupCohomology.map ((e.symm.toMonoidHom.comp (QuotientGroup.mk' r.ker)).comp (MonoidHom.id _))
          ((Rep.resFunctor (MonoidHom.id _)).map ι ≫ θ'') 2 := by
      refine map_eq_map_of_hom_eq hgrp _ _ (fun a => ?_) 2
      obtain ⟨v, rfl⟩ : ∃ v : (↥L)ˣ, Additive.ofMul v = a := ⟨Additive.toMul a, rfl⟩
      change iD.hom (Additive.ofMul (Units.map Φ.symm.toRingHom.toMonoidHom v)) =
        Additive.ofMul (Units.map Φ''.symm.toRingHom.toMonoidHom (Units.map (IntermediateField.inclusion hLL'' : ↥L →* ↥L'') v))
      apply Additive.toMul.injective
      apply Units.ext
      erw [hiD]
      change i (Φ.symm (v : ↥L)) = Φ''.symm (IntermediateField.inclusion hLL'' (v : ↥L))
      apply Φ''.injective
      rw [hcompat', RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    rw [key, h2, H, map_nsmul]
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup r.ker, Nat.card_congr eKer.toEquiv, mul_comm]

end S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower (solution)
