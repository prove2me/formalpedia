-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9444e8a7-e320-5448-a845-a1642f41cb9c

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_NumberField_PlaceDecomp_exists_fin_mul_forall_exists_finprod_smul_eq_of_tower
import Theorems.Thm_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp
import Theorems.Thm_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp.NumberField"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp.NumberField.PlaceDecomp IsMulCommutative"
set_option maxHeartbeats 4000000

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.exists_fin_mul_forall_exists_finprod_smul_eq_of_tower PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp exists_fin_mul_forall_exists_finprod_smul_eq_of_tower exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq"
namespace NormIndexSol
p2m_open "NumberField.PlaceDecomp NumberField"

open IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise

section places
variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem reps_congr (w : HeightOneSpectrum (𝓞 M)) (P Q : HeightOneSpectrum (𝓞 K))
    (hP : HeightOneSpectrum.under (𝓞 K) w = P) (hQ : HeightOneSpectrum.under (𝓞 K) w = Q) (n : ℕ) :
    (∃ c : Fin n → (HeightOneSpectrum.adicCompletion K P)ˣ,
      ∀ a : (HeightOneSpectrum.adicCompletion K P)ˣ, ∃ (i : Fin n) (b : (HeightOneSpectrum.adicCompletion M w)ˣ),
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp K M w), σ • b : (HeightOneSpectrum.adicCompletion M w)ˣ) :
            (HeightOneSpectrum.adicCompletion M w)ˣ) : HeightOneSpectrum.adicCompletion M w) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom K M (⟨w, hP⟩ : (P).Extension (𝓞 M))
            ((a * (c i)⁻¹ : (HeightOneSpectrum.adicCompletion K P)ˣ) : HeightOneSpectrum.adicCompletion K P)) →
    (∃ c : Fin n → (HeightOneSpectrum.adicCompletion K Q)ˣ,
      ∀ a : (HeightOneSpectrum.adicCompletion K Q)ˣ, ∃ (i : Fin n) (b : (HeightOneSpectrum.adicCompletion M w)ˣ),
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp K M w), σ • b : (HeightOneSpectrum.adicCompletion M w)ˣ) :
            (HeightOneSpectrum.adicCompletion M w)ˣ) : HeightOneSpectrum.adicCompletion M w) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom K M (⟨w, hQ⟩ : (Q).Extension (𝓞 M))
            ((a * (c i)⁻¹ : (HeightOneSpectrum.adicCompletion K Q)ˣ) : HeightOneSpectrum.adicCompletion K Q)) := by
  have hPQ : P = Q := hP.symm.trans hQ
  subst hPQ
  exact id

theorem reps_mono (w : HeightOneSpectrum (𝓞 M)) (P : HeightOneSpectrum (𝓞 K))
    (hP : HeightOneSpectrum.under (𝓞 K) w = P) (n n' : ℕ) (hn : n ≤ n') (hpos : 0 < n) :
    (∃ c : Fin n → (HeightOneSpectrum.adicCompletion K P)ˣ,
      ∀ a : (HeightOneSpectrum.adicCompletion K P)ˣ, ∃ (i : Fin n) (b : (HeightOneSpectrum.adicCompletion M w)ˣ),
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp K M w), σ • b : (HeightOneSpectrum.adicCompletion M w)ˣ) :
            (HeightOneSpectrum.adicCompletion M w)ˣ) : HeightOneSpectrum.adicCompletion M w) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom K M (⟨w, hP⟩ : (P).Extension (𝓞 M))
            ((a * (c i)⁻¹ : (HeightOneSpectrum.adicCompletion K P)ˣ) : HeightOneSpectrum.adicCompletion K P)) →
    (∃ c : Fin n' → (HeightOneSpectrum.adicCompletion K P)ˣ,
      ∀ a : (HeightOneSpectrum.adicCompletion K P)ˣ, ∃ (i : Fin n') (b : (HeightOneSpectrum.adicCompletion M w)ˣ),
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp K M w), σ • b : (HeightOneSpectrum.adicCompletion M w)ˣ) :
            (HeightOneSpectrum.adicCompletion M w)ˣ) : HeightOneSpectrum.adicCompletion M w) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom K M (⟨w, hP⟩ : (P).Extension (𝓞 M))
            ((a * (c i)⁻¹ : (HeightOneSpectrum.adicCompletion K P)ˣ) : HeightOneSpectrum.adicCompletion K P)) := by
  rintro ⟨c, hc⟩
  refine ⟨fun k => if hk : (k : ℕ) < n then c ⟨k, hk⟩ else c ⟨0, hpos⟩, fun a => ?_⟩
  obtain ⟨i, b, hb⟩ := hc a
  refine ⟨Fin.castLE hn i, b, ?_⟩
  have hi : ((Fin.castLE hn i : Fin n') : ℕ) < n := i.2
  simp only [Fin.val_castLE, Fin.is_lt, ↓reduceDIte, Fin.eta]
  exact hb

end places

section tower
variable (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F]

private theorem _root_.NumberField.PlaceDecomp.NormIndexSol.under_under (w : HeightOneSpectrum (𝓞 F)) :
    HeightOneSpectrum.under (𝓞 E) w = HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w) := by
  ext1
  simp [HeightOneSpectrum.under_asIdeal, Ideal.under_under]

p2m_export "NumberField.PlaceDecomp.NormIndexSol" "under_under"
omit [NumberField E] [NumberField L] in
theorem restrictScalars_smul_valuationSubring (σ : F ≃ₐ[L] F) (S : ValuationSubring F) :
    (σ.restrictScalars E) • S = σ • S := by
  ext x
  simp only [ValuationSubring.mem_smul_pointwise_iff_exists]
  rfl

omit [NumberField E] [NumberField L] in

theorem mem_decomp_iff_restrictScalars_mem (w : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[L] F) :
    σ ∈ NumberField.PlaceDecomp.decomp L F w ↔ σ.restrictScalars E ∈ NumberField.PlaceDecomp.decomp E F w := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, restrictScalars_smul_valuationSubring]

theorem card_decomp_le_of_tower (w : HeightOneSpectrum (𝓞 F)) :
    Nat.card ↥(NumberField.PlaceDecomp.decomp L F w) ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by
  classical
  refine Nat.card_le_card_of_injective
    (fun τ => (⟨(τ : F ≃ₐ[L] F).restrictScalars E, (mem_decomp_iff_restrictScalars_mem E L F w τ).mp τ.2⟩ :
      ↥(NumberField.PlaceDecomp.decomp E F w))) fun τ₁ τ₂ hτ => ?_
  exact Subtype.ext (AlgEquiv.restrictScalars_injective E (congrArg Subtype.val hτ))

omit [NumberField E] [NumberField L] [NumberField F] in

theorem restrictScalars_mul (a b : F ≃ₐ[L] F) :
    (a * b).restrictScalars E = a.restrictScalars E * b.restrictScalars E :=
  AlgEquiv.ext fun _ => rfl

end tower

section cards
variable (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem card_decomp_le_finrank [IsGalois K M] (w : HeightOneSpectrum (𝓞 M)) :
    Nat.card ↥(NumberField.PlaceDecomp.decomp K M w) ≤ Module.finrank K M := by
  rw [← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_le_card_group _

end cards

end NumberField.PlaceDecomp.NormIndexSol

namespace NumberField p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.exists_fin_mul_forall_exists_finprod_smul_eq_of_tower PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq" namespace PlaceDecomp p2m_export "NumberField.PlaceDecomp" "decomp exists_fin_mul_forall_exists_finprod_smul_eq_of_tower exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq" namespace NormIndexSol end NumberField.PlaceDecomp.NormIndexSol
p2m_open_scoped "NumberField NumberField.PlaceDecomp" in
open NumberField.PlaceDecomp.NormIndexSol _root_.NumberField.PlaceDecomp _root_.P2MW.S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp.NumberField.PlaceDecomp in

theorem NumberField.PlaceDecomp.NormIndexSol.main (N : ℕ) :
    ∀ (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
      (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
      [IsMulCommutative ↥(NumberField.PlaceDecomp.decomp E F w)],
      Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ≤ N →
      ∃ (n : ℕ) (c : Fin n → (v.adicCompletion E)ˣ), n ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ∧
        ∀ a : (HeightOneSpectrum.adicCompletion E v)ˣ, ∃ (i : Fin n) (b : (HeightOneSpectrum.adicCompletion F w)ˣ),
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (HeightOneSpectrum.adicCompletion F w)ˣ) :
            (HeightOneSpectrum.adicCompletion F w)ˣ) : HeightOneSpectrum.adicCompletion F w) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : (v).Extension (𝓞 F))
            ((a * (c i)⁻¹ : (HeightOneSpectrum.adicCompletion E v)ˣ) : HeightOneSpectrum.adicCompletion E v) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro E F _ _ _ _ _ _ v w hw _ hN
  classical

  let L₀ : IntermediateField E F := IntermediateField.fixedField (NumberField.PlaceDecomp.decomp E F w)
  have hfix : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ↥L₀), (σ : F ≃ₐ[E] F) (algebraMap (↥L₀) F x) = algebraMap (↥L₀) F x :=
    fun σ x => (IntermediateField.mem_fixedField_iff (NumberField.PlaceDecomp.decomp E F w) x.1).mp x.2 (σ : F ≃ₐ[E] F) σ.2

  have hres : ∀ τ : F ≃ₐ[↥L₀] F, τ.restrictScalars E ∈ NumberField.PlaceDecomp.decomp E F w := by
    intro τ
    have hτ : τ.restrictScalars E ∈ L₀.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact τ.commutes ⟨x, hx⟩
    rwa [IntermediateField.fixingSubgroup_fixedField] at hτ

  haveI hGab : IsMulCommutative (F ≃ₐ[↥L₀] F) := ⟨⟨fun a b => by
    apply AlgEquiv.restrictScalars_injective E
    rw [restrictScalars_mul E (↥L₀) F, restrictScalars_mul E (↥L₀) F]
    exact congrArg Subtype.val (mul_comm (⟨a.restrictScalars E, hres a⟩ : ↥(NumberField.PlaceDecomp.decomp E F w)) ⟨b.restrictScalars E, hres b⟩)⟩⟩
  have hcardG : Nat.card (F ≃ₐ[↥L₀] F) ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) :=
    Nat.card_le_card_of_injective (fun τ => (⟨τ.restrictScalars E, hres τ⟩ : ↥(NumberField.PlaceDecomp.decomp E F w)))
      fun τ₁ τ₂ hτ => AlgEquiv.restrictScalars_injective E (congrArg Subtype.val hτ)
  have hfinrank : Module.finrank (↥L₀) F ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by
    rw [← IsGalois.card_aut_eq_finrank]; exact hcardG
  haveI hDab : IsMulCommutative ↥(NumberField.PlaceDecomp.decomp (↥L₀) F w) :=
    ⟨⟨fun a b => Subtype.ext (mul_comm (a : F ≃ₐ[↥L₀] F) (b : F ≃ₐ[↥L₀] F))⟩⟩
  have hLE0 : HeightOneSpectrum.under (𝓞 E) w =
      HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 ↥L₀) w) := under_under E (↥L₀) F w

  suffices key : ∃ (m : ℕ) (d : Fin m → (HeightOneSpectrum.adicCompletion (↥L₀) (HeightOneSpectrum.under (𝓞 ↥L₀) w))ˣ),
      m ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ∧
      ∀ a : (HeightOneSpectrum.adicCompletion (↥L₀) (HeightOneSpectrum.under (𝓞 ↥L₀) w))ˣ, ∃ (i : Fin m) (b : (HeightOneSpectrum.adicCompletion F w)ˣ),
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp (↥L₀) F w), σ • b : (HeightOneSpectrum.adicCompletion F w)ˣ) :
            (HeightOneSpectrum.adicCompletion F w)ˣ) : HeightOneSpectrum.adicCompletion F w) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom (↥L₀) F (⟨w, rfl⟩ : ((HeightOneSpectrum.under (𝓞 ↥L₀) w)).Extension (𝓞 F))
            ((a * (d i)⁻¹ : (HeightOneSpectrum.adicCompletion (↥L₀) (HeightOneSpectrum.under (𝓞 ↥L₀) w))ˣ) : HeightOneSpectrum.adicCompletion (↥L₀) (HeightOneSpectrum.under (𝓞 ↥L₀) w)) by
    obtain ⟨m, d, hm, hd⟩ := key
    obtain ⟨c, hc⟩ := NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq
      E (↥L₀) F w hLE0 hfix m d hd
    obtain ⟨c', hc'⟩ := reps_congr w _ v hLE0 hw m ⟨c, hc⟩
    exact ⟨m, c', hm, hc'⟩

  by_cases hcyc : IsCyclic ↥(NumberField.PlaceDecomp.decomp (↥L₀) F w)
  · obtain ⟨m, d, hm, hd⟩ :=
      NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp
        (↥L₀) F (HeightOneSpectrum.under (𝓞 ↥L₀) w) w rfl
    exact ⟨m, d, hm.trans (card_decomp_le_of_tower E (↥L₀) F w), hd⟩

  have hnt : Nontrivial ↥(NumberField.PlaceDecomp.decomp (↥L₀) F w) := by
    by_contra hnt'
    rw [not_nontrivial_iff_subsingleton] at hnt'
    exact hcyc inferInstance
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥(NumberField.PlaceDecomp.decomp (↥L₀) F w))
  let H : Subgroup ↥(NumberField.PlaceDecomp.decomp (↥L₀) F w) := Subgroup.zpowers g
  have hHbot : H ≠ ⊥ := by simpa [H, Subgroup.zpowers_eq_bot] using hg
  have hHtop : H ≠ ⊤ := fun htop => hcyc ((isCyclic_iff_exists_zpowers_eq_top).mpr ⟨g, htop⟩)

  let H'' : Subgroup (F ≃ₐ[↥L₀] F) := H.map (NumberField.PlaceDecomp.decomp (↥L₀) F w).subtype
  haveI hHn : H''.Normal := Subgroup.normal_of_comm H''
  let L : IntermediateField (↥L₀) F := IntermediateField.fixedField H''
  haveI : IsGalois (↥L₀) (↥L) := IsGalois.of_fixedField_normal_subgroup H''

  have hcardH'' : Nat.card ↥H'' = Nat.card ↥H :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hLF : Module.finrank (↥L) F = Nat.card ↥H := by
    rw [IntermediateField.finrank_fixedField_eq_card, hcardH'']
  have hHlt : Nat.card ↥H < Nat.card ↥(NumberField.PlaceDecomp.decomp (↥L₀) F w) :=
    lt_of_le_of_ne (Subgroup.card_le_card_group H) (fun h => hHtop ((Subgroup.card_eq_iff_eq_top H).mp h))
  have hHgt : 1 < Nat.card ↥H := (Subgroup.one_lt_card_iff_ne_bot H).mpr hHbot
  have htower : Module.finrank (↥L₀) (↥L) * Module.finrank (↥L) F = Module.finrank (↥L₀) F :=
    Module.finrank_mul_finrank (↥L₀) (↥L) F
  have hD'le : Nat.card ↥(NumberField.PlaceDecomp.decomp (↥L₀) F w) ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) :=
    card_decomp_le_of_tower E (↥L₀) F w

  have hlt₁ : Nat.card ↥(NumberField.PlaceDecomp.decomp (↥L₀) (↥L) (HeightOneSpectrum.under (𝓞 ↥L) w)) < N := by
    have h1 := card_decomp_le_finrank (↥L₀) (↥L) (HeightOneSpectrum.under (𝓞 ↥L) w)
    have h2 : Module.finrank (↥L₀) (↥L) < Module.finrank (↥L₀) F := by
      rw [← htower, hLF]
      exact lt_mul_of_one_lt_right Module.finrank_pos hHgt
    omega
  have hlt₂ : Nat.card ↥(NumberField.PlaceDecomp.decomp (↥L) F w) < N := by
    have h1 := card_decomp_le_finrank (↥L) F w
    omega

  haveI : IsMulCommutative (↥L ≃ₐ[↥L₀] ↥L) := ⟨⟨fun s t => by
    obtain ⟨s, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥L₀) (K₁ := ↥L) F s
    obtain ⟨t, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥L₀) (K₁ := ↥L) F t
    rw [← map_mul, ← map_mul, mul_comm]⟩⟩
  haveI : IsMulCommutative ↥(NumberField.PlaceDecomp.decomp (↥L₀) (↥L) (HeightOneSpectrum.under (𝓞 ↥L) w)) :=
    ⟨⟨fun a b => Subtype.ext (mul_comm (a : ↥L ≃ₐ[↥L₀] ↥L) (b : ↥L ≃ₐ[↥L₀] ↥L))⟩⟩
  haveI : IsMulCommutative (F ≃ₐ[↥L] F) := ⟨⟨fun a b => by
    apply AlgEquiv.restrictScalars_injective (↥L₀)
    rw [restrictScalars_mul (↥L₀) (↥L) F, restrictScalars_mul (↥L₀) (↥L) F]
    exact mul_comm _ _⟩⟩
  haveI : IsMulCommutative ↥(NumberField.PlaceDecomp.decomp (↥L) F w) :=
    ⟨⟨fun a b => Subtype.ext (mul_comm (a : F ≃ₐ[↥L] F) (b : F ≃ₐ[↥L] F))⟩⟩

  obtain ⟨n, c, hn, hc⟩ := ih _ hlt₁ (↥L₀) (↥L)
    (HeightOneSpectrum.under (𝓞 ↥L₀) (HeightOneSpectrum.under (𝓞 ↥L) w)) (HeightOneSpectrum.under (𝓞 ↥L) w) rfl le_rfl
  obtain ⟨m, d, hm, hd⟩ := ih _ hlt₂ (↥L) F (HeightOneSpectrum.under (𝓞 ↥L) w) w rfl le_rfl

  have hLL0 : HeightOneSpectrum.under (𝓞 ↥L₀) w =
      HeightOneSpectrum.under (𝓞 ↥L₀) (HeightOneSpectrum.under (𝓞 ↥L) w) := under_under (↥L₀) (↥L) F w
  obtain ⟨c', hc'⟩ := NumberField.PlaceDecomp.exists_fin_mul_forall_exists_finprod_smul_eq_of_tower
    (↥L₀) (↥L) F w hLL0 n c hc m d hd
  obtain ⟨d₀, hd₀⟩ := reps_congr w _ (HeightOneSpectrum.under (𝓞 ↥L₀) w) hLL0 rfl (n * m) ⟨c', hc'⟩
  refine ⟨n * m, d₀, ?_, hd₀⟩

  calc n * m ≤ Module.finrank (↥L₀) (↥L) * Module.finrank (↥L) F :=
        Nat.mul_le_mul (hn.trans (card_decomp_le_finrank (↥L₀) (↥L) _)) (hm.trans (card_decomp_le_finrank (↥L) F w))
    _ = Module.finrank (↥L₀) F := htower
    _ ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := hfinrank

open NumberField.PlaceDecomp.NormIndexSol in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    [IsMulCommutative ↥(NumberField.PlaceDecomp.decomp E F w)] :
    ∃ (n : ℕ) (c : Fin n → (v.adicCompletion E)ˣ), n ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ∧
      ∀ a : (v.adicCompletion E)ˣ, ∃ (i : Fin n) (b : (w.adicCompletion F)ˣ),
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
            w.adicCompletion F) =
          IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))
            ((a * (c i)⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) :=
  main _ E F v w hw le_rfl

end S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp (solution)
