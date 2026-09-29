-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_isLocalFundamentalClass_map_eq_map_of_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ad7c1b47-1d8c-593c-90a1-b15568c5ddf2

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_NumberField_PlaceTransport_transport_eq_actRingEquiv
import Theorems.Thm_NumberField_PlaceTransport_transport_trans_transport
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_map_of_smul_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory NumberField P2MW.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_map_of_smul_eq.NumberField IsDedekindDomain"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_map_of_smul_eq.NumberField.PlaceDecomp NumberField.PlaceTransport"

namespace NumberField
p2m_export "NumberField" "mk place PlaceDecomp.decomp PlaceDecomp.smul_def PlaceDecomp.coe_smul_units PlaceTransport.transport"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp smul_def coe_smul_units"
namespace ConjFundProof
p2m_open "NumberField.PlaceDecomp NumberField"

open NumberField.PlaceTransport ExtCitation.LocalLevel

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
    [MulDistribMulAction G M] [MulDistribMulAction H N] (f : M →* N) (hf) (m : M) :
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

variable {E F : Type} [Field E] [Field F] [NumberField F] [Algebra E F]

theorem transport_congr {σ τ : F ≃ₐ[E] F} (hστ : σ = τ) {w w' : HeightOneSpectrum (𝓞 F)} (h : σ • w = w') (h' : τ • w = w') :
    transport σ h = transport τ h' := by
  subst hστ
  rfl

theorem mem_decomp_smul_iff (w : HeightOneSpectrum (𝓞 F)) (σ τ : F ≃ₐ[E] F) :
    τ ∈ decomp E F (σ • w) ↔ σ⁻¹ * τ * σ ∈ decomp E F w := by
  rw [← stabilizer_eq_decomp, ← stabilizer_eq_decomp, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    mul_smul, mul_smul, inv_smul_eq_iff]

theorem transport_smul (w : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (τ : ↥(decomp E F (σ • w)))
    (g : ↥(decomp E F w)) (hg : (g : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ) (y : w.adicCompletion F) :
    transport σ rfl (g • y) = τ • transport σ rfl y := by
  have hc : ((g : ↥(decomp E F w)) : F ≃ₐ[E] F) • w = w :=
    MulAction.mem_stabilizer_iff.mp (((SetLike.ext_iff.mp (stabilizer_eq_decomp E F w)) _).2 g.2)
  have hτ : ((τ : ↥(decomp E F (σ • w))) : F ≃ₐ[E] F) • (σ • w) = σ • w :=
    MulAction.mem_stabilizer_iff.mp (((SetLike.ext_iff.mp (stabilizer_eq_decomp E F (σ • w))) _).2 τ.2)
  have h₃ : (σ * (g : F ≃ₐ[E] F)) • w = σ • w := by
    rw [hg, show σ * (σ⁻¹ * (τ : F ≃ₐ[E] F) * σ) = (τ : F ≃ₐ[E] F) * σ by group, mul_smul, hτ]
  have h₃' : ((τ : F ≃ₐ[E] F) * σ) • w = σ • w := by rw [mul_smul, hτ]
  rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def, ← transport_eq_actRingEquiv E F w g hc,
    ← transport_eq_actRingEquiv E F (σ • w) τ hτ, ← RingEquiv.trans_apply, ← RingEquiv.trans_apply,
    transport_trans_transport E F σ _ hc rfl h₃, transport_trans_transport E F (τ : F ≃ₐ[E] F) σ rfl hτ h₃']
  exact congrFun (congrArg DFunLike.coe (transport_congr (by rw [hg]; group) h₃ h₃')) y

theorem isLocalFundamentalClass_map_of_twist (q : ℕ) [Fact q.Prime] (L' K₀ : IntermediateField ℚ_[q] (PadicAlgCl q))
    [FiniteDimensional ℚ_[q] K₀] (G G₁ : Type) [Group G] [Group G₁]
    [MulSemiringAction G L'] [MulDistribMulAction G (↥L')ˣ] [MulSemiringAction G₁ L'] [MulDistribMulAction G₁ (↥L')ˣ]
    (c : G₁ →* G) (cinv : G → G₁) (hcinv : ∀ g, c (cinv g) = g) (hinvc : ∀ τ, cinv (c τ) = τ)
    (hsmul : ∀ (τ : G₁) (x : ↥L'), τ • x = c τ • x) (hsmulu : ∀ (τ : G₁) (x : (↥L')ˣ), τ • x = c τ • x)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L')ˣ)) (hu : IsLocalFundamentalClass q L' G K₀ u)
    (ιc : Rep.res c (Rep.ofMulDistribMulAction G (↥L')ˣ) ⟶ Rep.ofMulDistribMulAction G₁ (↥L')ˣ)
    (hιc : ∀ v : (↥L')ˣ, ιc.hom (Additive.ofMul v) = Additive.ofMul v) :
    IsLocalFundamentalClass q L' G₁ K₀ ((groupCohomology.map c ιc 2).hom u) := by
  have hcbij : Function.Bijective c := ⟨Function.LeftInverse.injective hinvc, Function.RightInverse.surjective hcinv⟩
  let cEquiv : G₁ ≃* G := MulEquiv.ofBijective c hcbij
  unfold IsLocalFundamentalClass
  intro M _ hLM H _ _ _ _ _ NL Nn _ _ e₁ φ π d₁ ι₁ hι₁ hfin hcar

  let e : G ≃* H ⧸ NL := cEquiv.symm.trans e₁
  have d : IsUnramOverlayerDatum q L' G K₀ M hLM H NL Nn e φ π :=
    { smul_algebraMap := d₁.smul_algebraMap
      coe_smul_units := d₁.coe_smul_units
      mem_base_iff := d₁.mem_base_iff
      mem_layer_iff := d₁.mem_layer_iff
      coe_smul_eq := fun g h hgh x => by
        have h1 : (QuotientGroup.mk h : H ⧸ NL) = e₁ (cinv g) := by
          rw [hgh]
          change e₁ (cEquiv.symm g) = e₁ (cinv g)
          congr 1
          apply cEquiv.injective
          rw [MulEquiv.apply_symm_apply]
          exact (hcinv g).symm
        have := d₁.coe_smul_eq (cinv g) h h1 x
        rw [hsmul, hcinv] at this
        exact this
      card_quotient := d₁.card_quotient.trans (Nat.card_eq_of_bijective c hcbij)
      mem_zpowers := d₁.mem_zpowers
      frobenius := d₁.frobenius
      smul_pi := d₁.smul_pi
      pi_mem := d₁.pi_mem
      norm_pi_lt := d₁.norm_pi_lt
      norm_le_norm_pi := d₁.norm_le_norm_pi }

  let f₁ : (↥L')ˣ →* (↥M)ˣ := AddMonoidHom.toMultiplicative ι₁.hom.toLinearMap.toAddMonoidHom
  have hf₁ : ∀ v : (↥L')ˣ, ι₁.hom (Additive.ofMul v) = Additive.ofMul (f₁ v) := fun v => rfl
  have hι₁eq : ∀ (h : H) (v : (↥L')ˣ), f₁ ((e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) h • v) = h • f₁ v := by
    intro h v
    apply Additive.ofMul.injective
    have key := Rep.hom_comm_apply ι₁ h (Additive.ofMul v)
    have lhs : (Rep.res (e₁.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction G₁ (↥L')ˣ)).ρ h (Additive.ofMul v)
        = Additive.ofMul ((e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) h • v) := by
      change Additive.ofMul ((e₁.symm (QuotientGroup.mk h)) • v) = _
      rw [hsmulu]
      rfl
    rw [lhs] at key
    exact key
  let ι : Rep.res (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction G (↥L')ˣ) ⟶
      Rep.ofMulDistribMulAction H (↥M)ˣ := resRepHom _ f₁ hι₁eq
  have hι : ∀ v : (↥L')ˣ, (((Additive.toMul (ι.hom (Additive.ofMul v)) : (↥M)ˣ) : ↥M) : PadicAlgCl q) = ((v : ↥L') : PadicAlgCl q) :=
    fun v => hι₁ v
  have H0 := hu M hLM H NL Nn e φ π d ι hι hfin hcar

  have hgrp : c.comp (e₁.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) = e.symm.toMonoidHom.comp (QuotientGroup.mk' NL) := by
    ext h : 1
    rfl
  have key : groupCohomology.map (c.comp (e₁.symm.toMonoidHom.comp (QuotientGroup.mk' NL)))
      ((Rep.resFunctor (e₁.symm.toMonoidHom.comp (QuotientGroup.mk' NL))).map ιc ≫ ι₁) 2 =
      groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ι 2 := by
    refine map_eq_map_of_hom_eq hgrp _ _ (fun a => ?_) 2
    obtain ⟨v, rfl⟩ : ∃ v : (↥L')ˣ, Additive.ofMul v = a := ⟨Additive.toMul a, rfl⟩
    change ι₁.hom (ιc.hom (Additive.ofMul v)) = Additive.ofMul (f₁ v)
    rw [hιc]
    exact hf₁ v
  have h2 := groupCohomology.map_comp (A := Rep.ofMulDistribMulAction G (↥L')ˣ)
      (B := Rep.ofMulDistribMulAction G₁ (↥L')ˣ) (C := Rep.ofMulDistribMulAction H (↥M)ˣ)
      c (e₁.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ιc ι₁ 2
  rw [key] at h2
  have h2u := congrArg (fun (T : groupCohomology (Rep.ofMulDistribMulAction G (↥L')ˣ) 2 ⟶
      groupCohomology (Rep.ofMulDistribMulAction H (↥M)ˣ) 2) => T.hom u) h2
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2u
  change (groupCohomology.map (e₁.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ι₁ 2).hom ((groupCohomology.map c ιc 2).hom u) = _
  rw [← h2u]
  exact H0

theorem map_map_eq_map_map {k G G₁ : Type} [CommRing k] [Group G] [Group G₁] (c : G₁ →* G)
    {A B : Rep k G} {A₁ C : Rep k G₁} (θ : A ⟶ B) (T : Rep.res c B ⟶ C) (ιc : Rep.res c A ⟶ A₁) (θ₁ : A₁ ⟶ C)
    (hcomm : ∀ a : A, T.hom (θ.hom a) = θ₁.hom (ιc.hom a)) (n : ℕ) (u : groupCohomology A n) :
    (groupCohomology.map c T n).hom ((groupCohomology.map (MonoidHom.id G) θ n).hom u) =
      (groupCohomology.map (MonoidHom.id G₁) θ₁ n).hom ((groupCohomology.map c ιc n).hom u) := by
  have h1 := congrArg (fun S => S.hom u) (groupCohomology.map_comp (A := A) (B := B) (C := C) (MonoidHom.id G) c θ T n)
  have h2 := congrArg (fun S => S.hom u) (groupCohomology.map_comp (A := A) (B := A₁) (C := C) c (MonoidHom.id G₁) ιc θ₁ n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [← h1, ← h2]
  have hgrp : (MonoidHom.id G).comp c = c.comp (MonoidHom.id G₁) := by rw [MonoidHom.id_comp, MonoidHom.comp_id]
  exact congrArg (fun (S : groupCohomology A n ⟶ groupCohomology C n) => S.hom u)
    (map_eq_map_of_hom_eq hgrp _ _ (fun a => hcomm a) n)

end NumberField.PlaceDecomp.ConjFundProof

open _root_.NumberField.PlaceDecomp _root_.P2MW.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_map_of_smul_eq.NumberField.PlaceDecomp NumberField.PlaceDecomp.ConjFundProof NumberField.PlaceTransport ExtCitation.LocalLevel in
set_option maxHeartbeats 6400000 in

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w w₁ : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (hσ : σ • w = w₁)

    (c : ↥(NumberField.PlaceDecomp.decomp E F w₁) →* ↥(NumberField.PlaceDecomp.decomp E F w))
    (hc : ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w₁), ((c τ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ)
    (T : Rep.res c (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)
    (hT : ∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (T.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
      NumberField.PlaceTransport.transport σ hσ (x : w.adicCompletion F))

    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L']
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
    (Φ : w.adicCompletion F ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : w.adicCompletion F), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
    (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (_ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (y : L'))
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u) :
    Nat.card ↥(NumberField.PlaceDecomp.decomp E F w₁) = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ∧
    ∃ (_ : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) L')
      (_ : MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (↥L')ˣ)
      (Φ₁ : w₁.adicCompletion F ≃+* L')
      (θ₁ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (↥L')ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)
      (u₁ : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (↥L')ˣ)),
      (∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w₁)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y) ∧
      (∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w₁)) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L')) ∧
      (∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w₁)) (y : w₁.adicCompletion F), Φ₁ (g • y) = g • Φ₁ y) ∧
      ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w₁)) K₀ ∧
      (∀ y : (↥L')ˣ, ((Additive.toMul (θ₁.hom (Additive.ofMul y)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) = Φ₁.symm (y : L')) ∧
      ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w₁)) K₀ u₁ ∧
      (groupCohomology.map c T 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u) =
        (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w₁)) θ₁ 2).hom u₁ := by
  rename_i _ _ _ _ hq hcu hΦ _ hK₀ hθ hu
  subst hσ

  have hmem : ∀ g : ↥(decomp E F w), σ * (g : F ≃ₐ[E] F) * σ⁻¹ ∈ decomp E F (σ • w) := fun g =>
    (mem_decomp_smul_iff w σ _).2 (by simpa [mul_assoc] using g.2)
  let cinv : ↥(decomp E F w) → ↥(decomp E F (σ • w)) := fun g => ⟨σ * (g : F ≃ₐ[E] F) * σ⁻¹, hmem g⟩
  have hcinv : ∀ g, c (cinv g) = g := fun g => Subtype.ext (by rw [hc]; change σ⁻¹ * (σ * (g : F ≃ₐ[E] F) * σ⁻¹) * σ = _; group)
  have hinvc : ∀ τ, cinv (c τ) = τ := fun τ => Subtype.ext (by change σ * ((c τ : ↥(decomp E F w)) : F ≃ₐ[E] F) * σ⁻¹ = _; rw [hc]; group)
  have hcbij : Function.Bijective c := ⟨Function.LeftInverse.injective hinvc, Function.RightInverse.surjective hcinv⟩
  let cEquiv : ↥(decomp E F (σ • w)) ≃* ↥(decomp E F w) := MulEquiv.ofBijective c hcbij
  refine ⟨(Nat.card_eq_of_bijective c hcbij), ?_⟩

  letI msa₁ : MulSemiringAction (↥(decomp E F (σ • w))) L' := MulSemiringAction.compHom L' c
  letI mda₁ : MulDistribMulAction (↥(decomp E F (σ • w))) (↥L')ˣ := MulDistribMulAction.compHom (↥L')ˣ c
  have hsmul₁ : ∀ (τ : ↥(decomp E F (σ • w))) (x : ↥L'), τ • x = (c τ) • x := fun _ _ => rfl
  have hsmul₁u : ∀ (τ : ↥(decomp E F (σ • w))) (x : (↥L')ˣ), τ • x = (c τ) • x := fun _ _ => rfl

  let Φ₁ : (σ • w).adicCompletion F ≃+* L' := (transport σ (rfl : σ • w = σ • w)).symm.trans Φ
  have hΦ₁ : ∀ (τ : ↥(decomp E F (σ • w))) (y : (σ • w).adicCompletion F), Φ₁ (τ • y) = τ • Φ₁ y := by
    intro τ y
    obtain ⟨z, rfl⟩ : ∃ z, transport σ rfl z = y := ⟨(transport σ rfl).symm y, RingEquiv.apply_symm_apply _ _⟩
    change Φ ((transport σ rfl).symm (τ • transport σ rfl z)) = (c τ) • Φ ((transport σ rfl).symm (transport σ rfl z))
    rw [← transport_smul w σ τ (c τ) (hc τ), RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, hΦ]
  have hq₁ : ∀ (τ : ↥(decomp E F (σ • w))) (y : ℚ_[q]), τ • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y :=
    fun τ y => hq (c τ) y
  have hcu₁ : ∀ (τ : ↥(decomp E F (σ • w))) (y : (↥L')ˣ), ((τ • y : (↥L')ˣ) : L') = τ • (y : L') :=
    fun τ y => hcu (c τ) y
  have hBase₁ : IsBase q L' (↥(decomp E F (σ • w))) K₀ := by
    refine ⟨hK₀.le, fun x => (hK₀.mem_iff x).trans ⟨fun h τ => h (c τ), fun h g => ?_⟩⟩
    rw [← hcinv g]
    exact h (cinv g)

  let θ₁ : Rep.ofMulDistribMulAction (↥(decomp E F (σ • w))) (↥L')ˣ ⟶
      Rep.ofMulDistribMulAction (↥(decomp E F (σ • w))) ((σ • w).adicCompletion F)ˣ :=
    thetaOf L' (fun g u => NumberField.PlaceDecomp.coe_smul_units g u) Φ₁ hcu₁ hΦ₁
  let ιc : Rep.res c (Rep.ofMulDistribMulAction (↥(decomp E F w)) (↥L')ˣ) ⟶ Rep.ofMulDistribMulAction (↥(decomp E F (σ • w))) (↥L')ˣ :=
    resRepHom c (MonoidHom.id _) fun τ v => rfl
  let u₁ := (groupCohomology.map c ιc 2).hom u

  have hu₁ : IsLocalFundamentalClass q L' (↥(decomp E F (σ • w))) K₀ u₁ :=
    isLocalFundamentalClass_map_of_twist q L' K₀ (↥(decomp E F w)) (↥(decomp E F (σ • w))) c cinv hcinv hinvc hsmul₁ hsmul₁u u hu ιc
      (fun v => rfl)

  refine ⟨msa₁, mda₁, Φ₁, θ₁, u₁, hq₁, hcu₁, hΦ₁, hBase₁, fun y => rfl, hu₁, ?_⟩
  refine map_map_eq_map_map c θ T ιc θ₁ (fun a => ?_) 2 u
  obtain ⟨v, rfl⟩ : ∃ v : (↥L')ˣ, Additive.ofMul v = a := ⟨Additive.toMul a, rfl⟩
  apply Additive.toMul.injective
  apply Units.ext
  change ((Additive.toMul (T.hom (Additive.ofMul (Additive.toMul (θ.hom (Additive.ofMul v))))) : ((σ • w).adicCompletion F)ˣ) :
      (σ • w).adicCompletion F) = transport σ rfl (Φ.symm (v : ↥L'))
  rw [hT]
  congr 1
  exact hθ v

end S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_map_of_smul_eq
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_map_of_smul_eq (solution)
