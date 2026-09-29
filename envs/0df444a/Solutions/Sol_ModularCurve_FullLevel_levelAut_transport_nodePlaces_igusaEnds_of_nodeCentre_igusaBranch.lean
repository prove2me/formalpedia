-- Prove2me | solution 1 for ModularCurve.FullLevel.levelAut_transport_nodePlaces_igusaEnds_of_nodeCentre_igusaBranch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/75c1349a-24b1-5d99-b743-733ebb50580b

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne
import Theorems.Thm_IsLocalRing_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_ValuationSubring_isIntegral_and_exists_totallyRamified_layers_of_henselian
import Theorems.Thm_ValuationSubring_eq_of_constantsTower_of_forall_mem_iff
import Theorems.Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_levelAut_transport_nodePlaces_igusaEnds_of_nodeCentre_igusaBranch

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

namespace BranchTransportH1

variable {K : Type*} [Field K]

def inclHom (S : Subring K) (V : ValuationSubring K) (h : ∀ x ∈ S, x ∈ V) : ↥S →+* ↥V where
  toFun x := ⟨x.1, h x.1 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem coe_inclHom (S : Subring K) (V : ValuationSubring K) (h : ∀ x ∈ S, x ∈ V) (x : ↥S) :
    ((inclHom S V h x : ↥V) : K) = x := rfl

private theorem _root_.BranchTransportH1.mem_maximalIdeal_iff (V : ValuationSubring K) {x : K} (hx : x ∈ V) :
    (⟨x, hx⟩ : ↥V) ∈ maximalIdeal ↥V ↔ x = 0 ∨ x⁻¹ ∉ V := by
  rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]

p2m_export "BranchTransportH1" "mem_maximalIdeal_iff"

theorem not_mem_maximalIdeal_of_isUnit (S : Subring K) (V : ValuationSubring K) (h : ∀ x ∈ S, x ∈ V)
    {x : K} (hxS : x ∈ S) (hu : IsUnit (⟨x, hxS⟩ : ↥S)) (hxV : x ∈ V) : (⟨x, hxV⟩ : ↥V) ∉ maximalIdeal ↥V := by
  have h1 : IsUnit (inclHom S V h ⟨x, hxS⟩) := hu.map _
  intro hm
  exact (IsLocalRing.mem_maximalIdeal _).mp hm h1

theorem dvr_eq_of_le_of_ne_top (D V : ValuationSubring K) (hD : IsDiscreteValuationRing ↥D) (hle : D ≤ V) (hV : V ≠ ⊤) :
    V = D := by
  refine le_antisymm ?_ hle
  intro x hxV
  by_contra hxD
  have hx0 : x ≠ 0 := by rintro rfl; exact hxD D.zero_mem
  have hxinv : x⁻¹ ∈ D := (D.mem_or_inv_mem x).resolve_left hxD
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥D
  have hunitK : ∀ v : (↥D)ˣ, ((v : ↥D) : K) * (((v⁻¹ : (↥D)ˣ) : ↥D) : K) = 1 := fun v => by
    have h := v.mul_inv
    rw [Subtype.ext_iff] at h
    exact h
  have hxi0 : (⟨x⁻¹, hxinv⟩ : ↥D) ≠ 0 := fun h => by
    have := congrArg Subtype.val h
    exact inv_ne_zero hx0 this
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxi0 hϖ
  have huK : x⁻¹ = ((u : ↥D) : K) * (ϖ : K) ^ n := by
    have := congrArg Subtype.val hu
    simpa using this
  have hn : n ≠ 0 := by
    rintro rfl
    apply hxD
    rw [pow_zero, mul_one] at huK
    have hxu : x = (((u⁻¹ : (↥D)ˣ) : ↥D) : K) := by
      have h2 := hunitK u
      rw [← huK] at h2
      calc x = x * (x⁻¹ * (((u⁻¹ : (↥D)ˣ) : ↥D) : K)) := by rw [h2, mul_one]
        _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
    rw [hxu]; exact SetLike.coe_mem _
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)

  have hϖinv : (ϖ : K)⁻¹ ∈ V := by
    have hrepr : (ϖ : K)⁻¹ = (ϖ : K) ^ (n - 1) * ((u : ↥D) : K) * x := by
      have hx' : x = (((u : ↥D) : K) * (ϖ : K) ^ n)⁻¹ := by rw [← huK, inv_inv]
      rw [hx']
      field_simp
      rw [← pow_succ']
      congr 1
      omega
    rw [hrepr]
    exact mul_mem (mul_mem (pow_mem (hle ϖ.2) _) (hle (u : ↥D).2)) hxV
  apply hV
  ext y
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  by_cases hyD : y ∈ D
  · exact hle hyD
  · have hy0 : y ≠ 0 := by rintro rfl; exact hyD D.zero_mem
    have hyinv : y⁻¹ ∈ D := (D.mem_or_inv_mem y).resolve_left hyD
    have hyi0 : (⟨y⁻¹, hyinv⟩ : ↥D) ≠ 0 := fun h => by
      have := congrArg Subtype.val h
      exact inv_ne_zero hy0 this
    obtain ⟨m, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hyi0 hϖ
    have hyK : y⁻¹ = ((u' : ↥D) : K) * (ϖ : K) ^ m := by
      have := congrArg Subtype.val hu'
      simpa using this
    have hyrepr : y = (((u'⁻¹ : (↥D)ˣ) : ↥D) : K) * ((ϖ : K)⁻¹) ^ m := by
      have : y = (y⁻¹)⁻¹ := (inv_inv y).symm
      rw [this, hyK, mul_inv, inv_pow]
      congr 1
      exact (eq_inv_of_mul_eq_one_right (hunitK u')).symm
    rw [hyrepr]
    exact mul_mem (hle (SetLike.coe_mem _)) (pow_mem hϖinv _)

end BranchTransportH1
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_levelAut_transport_nodePlaces_igusaEnds_of_nodeCentre_igusaBranch.BranchTransportH1"

open BranchTransportH1 in

theorem EqvTransportBody.branchTransport
    (K : Type) [Field K] (e : K ≃+* K)
    (O O' : Subring K) (hO : ∀ x : K, x ∈ O ↔ e x ∈ O')
    [IsLocalRing ↥O'] [IsNoetherianRing ↥O']

    (W₀ : ValuationSubring K) (hOW₀ : ∀ x ∈ O, x ∈ W₀) (hO'W₀ : ∀ x ∈ O', x ∈ W₀)
    (heW₀ : ∀ x : K, x ∈ W₀ ↔ e x ∈ W₀)

    (π : K) (hπ0 : π ≠ 0) (hπO : π ∈ O) (hπO' : π ∈ O') (hπe : e π = π)
    (hπW₀ : ∀ h : π ∈ W₀, (⟨π, h⟩ : ↥W₀) ∈ maximalIdeal ↥W₀)

    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : maximalIdeal W = Ideal.span {ϖ}) (w : ℕ) (hw : 1 ≤ w)
    (ι : AdicCompletion (maximalIdeal ↥O') ↥O' ≃+* UVCrossingModel W (ϖ ^ w))
    (hι : ι (algebraMap ↥O' (AdicCompletion (maximalIdeal ↥O') ↥O') ⟨π, hπO'⟩) = UVCrossingModel.const (ϖ ^ w) ϖ)
    (hfrac : ∀ x : K, ∃ r s : K, r ∈ O' ∧ s ∈ O' ∧ s ≠ 0 ∧ x * s = r)

    (d : K) (hdO' : d ∈ O') (hdW₀ : ∀ h : d ∈ W₀, (⟨d, h⟩ : ↥W₀) ∉ maximalIdeal ↥W₀)

    (D D' : ValuationSubring K) (hOD : ∀ x ∈ O, x ∈ D) (hO'D' : ∀ x ∈ O', x ∈ D')
    (hπD : ∀ h : π ∈ D, (⟨π, h⟩ : ↥D) ∈ maximalIdeal ↥D) (hπD' : ∀ h : π ∈ D', (⟨π, h⟩ : ↥D') ∈ maximalIdeal ↥D')
    (hD' : IsDiscreteValuationRing ↥D')
    (hdD' : ∀ h : d ∈ D', (⟨d, h⟩ : ↥D') ∈ maximalIdeal ↥D')

    (c : K) (hcO : c ∈ O) (hcW₀ : ∀ h : c ∈ W₀, (⟨c, h⟩ : ↥W₀) ∈ maximalIdeal ↥W₀)
    (hcD : ∀ h : c ∈ D, (⟨c, h⟩ : ↥D) ∉ maximalIdeal ↥D)
    (c' : K) (hc'O' : c' ∈ O') (hc'W₀ : ∀ h : c' ∈ W₀, (⟨c', h⟩ : ↥W₀) ∈ maximalIdeal ↥W₀)
    (hc'D' : ∀ h : c' ∈ D', (⟨c', h⟩ : ↥D') ∉ maximalIdeal ↥D') :
    ∀ x : K, x ∈ D ↔ e x ∈ D' := by
  classical
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ

  have hsymm : ∀ x : K, x ∈ O' ↔ e.symm x ∈ O := fun x => by
    rw [hO (e.symm x), RingEquiv.apply_symm_apply]
  let eO : ↥O ≃+* ↥O' :=
    { toFun := fun x => ⟨e x, (hO x).mp x.2⟩
      invFun := fun y => ⟨e.symm y, (hsymm y).mp y.2⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply (x : K))
      right_inv := fun y => Subtype.ext (e.apply_symm_apply (y : K))
      map_mul' := fun x y => Subtype.ext (map_mul e (x : K) (y : K))
      map_add' := fun x y => Subtype.ext (map_add e (x : K) (y : K)) }

  have hmW₀ : ∀ (x : K) (h : x ∈ W₀) (h' : e x ∈ W₀),
      (⟨x, h⟩ : ↥W₀) ∈ maximalIdeal ↥W₀ ↔ (⟨e x, h'⟩ : ↥W₀) ∈ maximalIdeal ↥W₀ := by
    intro x h h'
    rw [mem_maximalIdeal_iff, mem_maximalIdeal_iff, ← map_inv₀, ← heW₀, map_eq_zero_iff _ e.injective]
  have hsπ : e.symm π = π := by conv_lhs => rw [← hπe]; exact e.symm_apply_apply π

  let Q : Ideal ↥O := (maximalIdeal ↥D).comap (inclHom O D hOD)
  let Q' : Ideal ↥O' := (maximalIdeal ↥D').comap (inclHom O' D' hO'D')
  let Pss : Ideal ↥O' := (maximalIdeal ↥W₀).comap (inclHom O' W₀ hO'W₀)
  let Qe : Ideal ↥O' := Q.comap eO.symm.toRingHom
  have hQ : ∀ y : ↥O, y ∈ Q ↔ (⟨(y : K), hOD _ y.2⟩ : ↥D) ∈ maximalIdeal ↥D := fun _ => Iff.rfl
  have hQ' : ∀ y : ↥O', y ∈ Q' ↔ (⟨(y : K), hO'D' _ y.2⟩ : ↥D') ∈ maximalIdeal ↥D' := fun _ => Iff.rfl
  have hPss : ∀ y : ↥O', y ∈ Pss ↔ (⟨(y : K), hO'W₀ _ y.2⟩ : ↥W₀) ∈ maximalIdeal ↥W₀ := fun _ => Iff.rfl
  have hQe : ∀ y : ↥O', y ∈ Qe ↔ (⟨e.symm y, hOD _ ((hsymm y).mp y.2)⟩ : ↥D) ∈ maximalIdeal ↥D := fun _ => Iff.rfl
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
  haveI : Pss.IsPrime := Ideal.comap_isPrime _ _
  haveI : Qe.IsPrime := Ideal.comap_isPrime _ _

  have hπQe : (⟨π, hπO'⟩ : ↥O') ∈ Qe := by
    rw [hQe]
    have h1 : (⟨e.symm ((⟨π, hπO'⟩ : ↥O') : K), hOD _ ((hsymm _).mp hπO')⟩ : ↥D) = ⟨π, hOD _ hπO⟩ := Subtype.ext hsπ
    rw [h1]; exact hπD _
  have hπQ' : (⟨π, hπO'⟩ : ↥O') ∈ Q' := hπD' _
  have hπPss : (⟨π, hπO'⟩ : ↥O') ∈ Pss := hπW₀ _

  have hecO' : e c ∈ O' := (hO c).mp hcO
  have hecW₀m : ∀ h : e c ∈ W₀, (⟨e c, h⟩ : ↥W₀) ∈ maximalIdeal ↥W₀ := fun h => (hmW₀ c (hOW₀ c hcO) h).mp (hcW₀ _)
  have hecQe : (⟨e c, hecO'⟩ : ↥O') ∉ Qe := by
    rw [hQe]
    have h1 : (⟨e.symm ((⟨e c, hecO'⟩ : ↥O') : K), hOD _ ((hsymm _).mp hecO')⟩ : ↥D) = ⟨c, hOD _ hcO⟩ :=
      Subtype.ext (e.symm_apply_apply c)
    rw [h1]; exact hcD _
  have hecPss : (⟨e c, hecO'⟩ : ↥O') ∈ Pss := hecW₀m _
  have hec_nu : ¬ IsUnit (⟨e c, hecO'⟩ : ↥O') := fun hu =>
    not_mem_maximalIdeal_of_isUnit O' W₀ hO'W₀ hecO' hu (hO'W₀ _ hecO') (hecW₀m _)
  have hc'Q' : (⟨c', hc'O'⟩ : ↥O') ∉ Q' := hc'D' _
  have hc'Pss : (⟨c', hc'O'⟩ : ↥O') ∈ Pss := hc'W₀ _
  have hc'_nu : ¬ IsUnit (⟨c', hc'O'⟩ : ↥O') := fun hu =>
    not_mem_maximalIdeal_of_isUnit O' W₀ hO'W₀ hc'O' hu (hO'W₀ _ hc'O') (hc'W₀ _)
  have hdPss : (⟨d, hdO'⟩ : ↥O') ∉ Pss := hdW₀ _
  have hd_nu : ¬ IsUnit (⟨d, hdO'⟩ : ↥O') := fun hu =>
    not_mem_maximalIdeal_of_isUnit O' D' hO'D' hdO' hu (hO'D' _ hdO') (hdD' _)
  have hQe_ne : Qe ≠ maximalIdeal ↥O' := fun h => hecQe (by rw [h]; exact (IsLocalRing.mem_maximalIdeal _).mpr hec_nu)
  have hQ'_ne : Q' ≠ maximalIdeal ↥O' := fun h => hc'Q' (by rw [h]; exact (IsLocalRing.mem_maximalIdeal _).mpr hc'_nu)
  have hPss_ne : Pss ≠ maximalIdeal ↥O' := fun h => hdPss (by rw [h]; exact (IsLocalRing.mem_maximalIdeal _).mpr hd_nu)
  have hPssQe : Pss ≠ Qe := fun h => hecQe (h ▸ hecPss)
  have hPssQ' : Pss ≠ Q' := fun h => hc'Q' (h ▸ hc'Pss)

  have hkey : Qe = Q' := by
    by_contra hne
    have A1 := ModularCurve.UVCrossingModel.mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne ϖ hϖ w hw ι
      ⟨π, hπO'⟩ hι Qe Q' hne hπQe hπQ' hQe_ne hQ'_ne
    have A2 := ModularCurve.UVCrossingModel.mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne ϖ hϖ w hw ι
      ⟨π, hπO'⟩ hι Pss Qe hPssQe hπPss hπQe hPss_ne hQe_ne
    rcases A1 with ⟨hQeU, hQ'V⟩ | ⟨hQeV, hQ'U⟩ <;> rcases A2 with ⟨hPU, hQeV'⟩ | ⟨hPV, hQeU'⟩
    · exact hne (Ideal.ext fun f => (hQeV' f).trans (hQ'V f).symm)
    · exact hPssQ' (Ideal.ext fun f => (hPV f).trans (hQ'V f).symm)
    · exact hPssQ' (Ideal.ext fun f => (hPU f).trans (hQ'U f).symm)
    · exact hne (Ideal.ext fun f => (hQeU' f).trans (hQ'U f).symm)

  have hback : ∀ x : K, e x ∈ D' → x ∈ D := by
    intro x hx
    have hP : ∀ b : ↥O', b ∈ Q' ↔ O'.subtype b ∈ D'.nonunits := fun b => by
      rw [hQ']; exact ValuationSubring.coe_mem_nonunits_iff.symm
    obtain ⟨r₀, s₀, hr₀, hs₀, hs₀0, hxs⟩ := hfrac (e x)
    obtain ⟨r, s, hsQ', hrs⟩ :=
      IsLocalRing.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
        ϖ hϖirr w hw ι O'.subtype Subtype.val_injective D' (fun b => hO'D' _ b.2) Q' hP hQ'_ne (e x) hx
        ⟨⟨r₀, hr₀⟩, ⟨s₀, hs₀⟩, fun h => hs₀0 (congrArg Subtype.val h), hxs⟩
    have hsQe : s ∉ Qe := by rw [hkey]; exact hsQ'
    have hs' : (⟨e.symm s, hOD _ ((hsymm _).mp s.2)⟩ : ↥D) ∉ maximalIdeal ↥D := (hQe s).not.mp hsQe
    rw [mem_maximalIdeal_iff, not_or, not_not] at hs'
    obtain ⟨hs0, hsinv⟩ := hs'
    have hrO : e.symm r ∈ O := (hsymm _).mp r.2
    have hxrepr : x = e.symm r * (e.symm s)⁻¹ := by
      have h1 : x * e.symm s = e.symm r := by
        have := congrArg e.symm hrs
        rwa [map_mul, e.symm_apply_apply] at this
      rw [← h1, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
    rw [hxrepr]
    exact D.mul_mem _ _ (hOD _ hrO) hsinv
  intro x
  constructor
  ·
    intro hxD
    let V' : ValuationSubring K := D.comap e.symm.toRingHom
    have hmemV' : ∀ y : K, y ∈ V' ↔ e.symm y ∈ D := fun _ => Iff.rfl
    have hle : D' ≤ V' := fun y hy => (hmemV' y).mpr (hback (e.symm y) (by rw [e.apply_symm_apply]; exact hy))
    have hV' : V' ≠ ⊤ := fun h => by
      have h1 : π⁻¹ ∈ V' := h ▸ ValuationSubring.mem_top _
      rw [hmemV', map_inv₀, hsπ] at h1
      have h2 := hπD (hOD _ hπO)
      rw [mem_maximalIdeal_iff] at h2
      rcases h2 with h2 | h2
      · exact hπ0 h2
      · exact h2 h1
    have hVeq := BranchTransportH1.dvr_eq_of_le_of_ne_top D' V' hD' hle hV'
    have h3 : e x ∈ V' := by rw [hmemV', e.symm_apply_apply]; exact hxD
    rw [hVeq] at h3
    exact h3
  · exact hback x

namespace NodeTransportH2

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem evalAt_smul_apply (σ : F ≃ₐ[L] F) (v : Place L F) (f : F) : (σ • v).evalAt (σ f) = v.evalAt f := by
  classical
  by_cases hf : f ∈ v.toValuationSubring
  · have hf' : σ f ∈ (σ • v).toValuationSubring := (Place.Transport.mem_smul_iff' σ v f).mpr hf
    rw [(σ • v).evalAt_of_mem hf', v.evalAt_of_mem hf, Place.Transport.residue_smul σ v hf hf']
    set x := residue ↥v.toValuationSubring ⟨f, hf⟩
    set E := Place.smulResidueAlgEquiv σ v
    by_cases hx : ∃ a : L, algebraMap L v.ResidueField a = x
    · obtain ⟨a, ha⟩ := hx
      rw [← ha, AlgEquiv.commutes, Place.residueInv_algebraMap, Place.residueInv_algebraMap]
    · have hx' : ¬ ∃ a : L, algebraMap L (σ • v).ResidueField a = E x := by
        rintro ⟨a, ha⟩
        exact hx ⟨a, by rw [← E.commutes] at ha; exact E.injective ha⟩
      unfold Place.residueInv
      rw [Function.invFun_neg hx, Function.invFun_neg hx']
  · have hf' : σ f ∉ (σ • v).toValuationSubring := fun h => hf ((Place.Transport.mem_smul_iff' σ v f).mp h)
    rw [Place.evalAt, Place.evalAt, dif_neg hf, dif_neg hf']

theorem evalAt_inv_smul (σ : F ≃ₐ[L] F) (v : Place L F) (f : F) : (σ⁻¹ • v).evalAt f = v.evalAt (σ f) := by
  conv_lhs => rw [show f = σ⁻¹ (σ f) by rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]]
  exact evalAt_smul_apply σ⁻¹ v (σ f)

private theorem _root_.NodeTransportH2.mem_maximalIdeal_iff (V : ValuationSubring F) {x : F} (hx : x ∈ V) :
    (⟨x, hx⟩ : ↥V) ∈ maximalIdeal ↥V ↔ x = 0 ∨ x⁻¹ ∉ V := by
  rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]

p2m_export "NodeTransportH2" "mem_maximalIdeal_iff"

theorem mem_maximalIdeal_smul_iff {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (σ : Fb ≃ₐ[K] Fb) (v : Place K Fb)
    {y : Fb} (hy : y ∈ v.toValuationSubring) (hy' : σ y ∈ (σ • v).toValuationSubring) :
    (⟨σ y, hy'⟩ : ↥(σ • v).toValuationSubring) ∈ maximalIdeal ↥(σ • v).toValuationSubring ↔
      (⟨y, hy⟩ : ↥v.toValuationSubring) ∈ maximalIdeal ↥v.toValuationSubring := by
  rw [mem_maximalIdeal_iff, mem_maximalIdeal_iff, ← map_inv₀, Place.Transport.mem_smul_iff', map_eq_zero_iff _ σ.injective]

end NodeTransportH2
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_levelAut_transport_nodePlaces_igusaEnds_of_nodeCentre_igusaBranch.BranchTransportH1"

open NodeTransportH2 in

theorem EqvTransportBody.nodeDataTransport
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    (τ : F ≃ₐ[L] F)
    {K₀ : Type*} [CommRing K₀] (emb : K₀ →+* F)
    (τ₀ : K₀ ≃+* K₀) (hτ₀ : ∀ x : K₀, emb (τ₀ x) = τ (emb x))
    (O O' : Subring K₀) (hOO' : ∀ x : K₀, x ∈ O ↔ τ₀ x ∈ O')
    (S S' : Set (Place L F))
    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : K₀, f ∈ O → emb f ∈ P.toValuationSubring) ∧
      (∀ (f : K₀) (hf : f ∈ O), ¬ IsUnit (⟨f, hf⟩ : ↥O) →
        ∃ h : P.evalAt (emb f) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))
    (hS' : ∀ P : Place L F, P ∈ S' ↔
      (∀ f : K₀, f ∈ O' → emb f ∈ P.toValuationSubring) ∧
      (∀ (f : K₀) (hf : f ∈ O'), ¬ IsUnit (⟨f, hf⟩ : ↥O') →
        ∃ h : P.evalAt (emb f) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) :
    AlgebraicCurve.RegularProlongation.smulDisc τ S = S' ∧
    ∀ (Fbar : Type*) [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
      (R : AlgebraicCurve.RegularProlongation A F Fbar)
      (hτ : ∀ f : F, τ f ∈ R.integers ↔ f ∈ R.integers)
      (nd nd' : Place (ResidueField ↥A) Fbar),
      (∀ (f : K₀) (_ : f ∈ O) (hR : emb f ∈ R.integers), R.residue ⟨emb f, hR⟩ ∈ nd.toValuationSubring) →
      (∀ (f : K₀) (hf : f ∈ O) (hR : emb f ∈ R.integers), ¬ IsUnit (⟨f, hf⟩ : ↥O) →
        ∃ hm : R.residue ⟨emb f, hR⟩ ∈ nd.toValuationSubring,
          (⟨_, hm⟩ : ↥nd.toValuationSubring) ∈ maximalIdeal ↥nd.toValuationSubring) →
      (∀ y : Place (ResidueField ↥A) Fbar,
        (∀ (f : K₀) (_ : f ∈ O') (hR : emb f ∈ R.integers), R.residue ⟨emb f, hR⟩ ∈ y.toValuationSubring) →
        (∀ (f : K₀) (hf : f ∈ O') (hR : emb f ∈ R.integers), ¬ IsUnit (⟨f, hf⟩ : ↥O') →
          ∃ hm : R.residue ⟨emb f, hR⟩ ∈ y.toValuationSubring,
            (⟨_, hm⟩ : ↥y.toValuationSubring) ∈ maximalIdeal ↥y.toValuationSubring) →
        y = nd') →
      R.resAut τ hτ • nd = nd' := by

  have hsymm : ∀ x : K₀, x ∈ O' ↔ τ₀.symm x ∈ O := fun x => by
    rw [hOO' (τ₀.symm x), RingEquiv.apply_symm_apply]
  let eO : ↥O ≃+* ↥O' :=
    { toFun := fun x => ⟨τ₀ x, (hOO' x).mp x.2⟩
      invFun := fun y => ⟨τ₀.symm y, (hsymm y).mp y.2⟩
      left_inv := fun x => Subtype.ext (τ₀.symm_apply_apply (x : K₀))
      right_inv := fun y => Subtype.ext (τ₀.apply_symm_apply (y : K₀))
      map_mul' := fun x y => Subtype.ext (map_mul τ₀ (x : K₀) (y : K₀))
      map_add' := fun x y => Subtype.ext (map_add τ₀ (x : K₀) (y : K₀)) }
  have heO : ∀ x : ↥O, ((eO x : ↥O') : K₀) = τ₀ x := fun _ => rfl
  have hunit : ∀ (f : K₀) (hf : f ∈ O) (hf' : τ₀ f ∈ O'), IsUnit (⟨f, hf⟩ : ↥O) ↔ IsUnit (⟨τ₀ f, hf'⟩ : ↥O') := by
    intro f hf hf'
    have : (⟨τ₀ f, hf'⟩ : ↥O') = eO ⟨f, hf⟩ := Subtype.ext rfl
    rw [this, MulEquiv.isUnit_map]
  have hunit' : ∀ (f : K₀) (hf : f ∈ O') (hf' : τ₀.symm f ∈ O), IsUnit (⟨f, hf⟩ : ↥O') ↔ IsUnit (⟨τ₀.symm f, hf'⟩ : ↥O) := by
    intro f hf hf'
    rw [hunit (τ₀.symm f) hf' (by rw [RingEquiv.apply_symm_apply]; exact hf)]
    exact iff_of_eq (by congr 2; exact (τ₀.apply_symm_apply f).symm)
  have hτemb : ∀ x : K₀, τ.symm (emb x) = emb (τ₀.symm x) := fun x => by
    apply τ.injective; rw [AlgEquiv.apply_symm_apply, ← hτ₀, RingEquiv.apply_symm_apply]
  refine ⟨?_, ?_⟩
  ·
    ext P
    rw [AlgebraicCurve.RegularProlongation.mem_smulDisc_iff, hS, hS']
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => ?_, fun f hf hu => ?_⟩
      · have h := h1 (τ₀.symm f) ((hsymm f).mp hf)
        rw [Place.Transport.mem_inv_smul_iff, ← hτ₀, RingEquiv.apply_symm_apply] at h
        exact h
      · have hu' : ¬ IsUnit (⟨τ₀.symm f, (hsymm f).mp hf⟩ : ↥O) := fun h => hu ((hunit' f hf _).mpr h)
        obtain ⟨h, hm⟩ := h2 (τ₀.symm f) ((hsymm f).mp hf) hu'
        have hev : (τ⁻¹ • P).evalAt (emb (τ₀.symm f)) = P.evalAt (emb f) := by
          rw [evalAt_inv_smul, ← hτ₀, RingEquiv.apply_symm_apply]
        refine ⟨hev ▸ h, ?_⟩
        convert hm using 2
        exact hev.symm
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => ?_, fun f hf hu => ?_⟩
      · rw [Place.Transport.mem_inv_smul_iff, ← hτ₀]
        exact h1 (τ₀ f) ((hOO' f).mp hf)
      · have hu' : ¬ IsUnit (⟨τ₀ f, (hOO' f).mp hf⟩ : ↥O') := fun h => hu ((hunit f hf _).mpr h)
        obtain ⟨h, hm⟩ := h2 (τ₀ f) ((hOO' f).mp hf) hu'
        have hev : (τ⁻¹ • P).evalAt (emb f) = P.evalAt (emb (τ₀ f)) := by
          rw [evalAt_inv_smul, ← hτ₀]
        refine ⟨hev ▸ h, ?_⟩
        convert hm using 2
  ·
    intro Fbar _ _ R hτ nd nd' hC1 hC2 huniq
    apply huniq
    · intro f hf hR
      have hf₀ : τ₀.symm f ∈ O := (hsymm f).mp hf
      have hR₀ : emb (τ₀.symm f) ∈ R.integers := by
        rw [← hτemb, ← AlgEquiv.aut_inv]; exact (R.symm_mem_integers_iff τ hτ _).mpr hR
      have key : R.residue ⟨emb f, hR⟩ = R.resAut τ hτ (R.residue ⟨emb (τ₀.symm f), hR₀⟩) := by
        rw [AlgebraicCurve.RegularProlongation.resAut_residue]
        congr 1
        apply Subtype.ext
        show emb f = τ (emb (τ₀.symm f))
        rw [← hτ₀, RingEquiv.apply_symm_apply]
      rw [key]
      exact (Place.Transport.mem_smul_iff' _ nd _).mpr (hC1 _ hf₀ hR₀)
    · intro f hf hR hu
      have hf₀ : τ₀.symm f ∈ O := (hsymm f).mp hf
      have hR₀ : emb (τ₀.symm f) ∈ R.integers := by
        rw [← hτemb, ← AlgEquiv.aut_inv]; exact (R.symm_mem_integers_iff τ hτ _).mpr hR
      have hu₀ : ¬ IsUnit (⟨τ₀.symm f, hf₀⟩ : ↥O) := fun h => hu ((hunit' f hf hf₀).mpr h)
      obtain ⟨hm₀, hmax₀⟩ := hC2 _ hf₀ hR₀ hu₀
      have key : R.residue ⟨emb f, hR⟩ = R.resAut τ hτ (R.residue ⟨emb (τ₀.symm f), hR₀⟩) := by
        rw [AlgebraicCurve.RegularProlongation.resAut_residue]
        congr 1
        apply Subtype.ext
        show emb f = τ (emb (τ₀.symm f))
        rw [← hτ₀, RingEquiv.apply_symm_apply]
      have hm : R.residue ⟨emb f, hR⟩ ∈ (R.resAut τ hτ • nd).toValuationSubring := by
        rw [key]; exact (Place.Transport.mem_smul_iff' _ nd _).mpr hm₀
      refine ⟨hm, ?_⟩
      have hm' : R.resAut τ hτ (R.residue ⟨emb (τ₀.symm f), hR₀⟩) ∈ (R.resAut τ hτ • nd).toValuationSubring := by
        rw [← key]; exact hm
      have h2 := (mem_maximalIdeal_smul_iff (R.resAut τ hτ) nd hm₀ hm').mpr hmax₀
      convert h2 using 2

namespace EqvTransportBody

def restrictEquiv {K E : Type*} [Field K] [Field E] [Algebra K E] (S : IntermediateField K E) (τ : E ≃+* E)
    (h₁ : ∀ x : E, x ∈ S → τ x ∈ S) (h₂ : ∀ x : E, x ∈ S → τ.symm x ∈ S) : ↥S ≃+* ↥S where
  toFun x := ⟨τ x, h₁ x x.2⟩
  invFun y := ⟨τ.symm y, h₂ y y.2⟩
  left_inv x := Subtype.ext (τ.symm_apply_apply (x : E))
  right_inv y := Subtype.ext (τ.apply_symm_apply (y : E))
  map_mul' x y := Subtype.ext (map_mul τ (x : E) (y : E))
  map_add' x y := Subtype.ext (map_add τ (x : E) (y : E))

@[scoped simp] theorem coe_restrictEquiv {K E : Type*} [Field K] [Field E] [Algebra K E] (S : IntermediateField K E) (τ : E ≃+* E)
    (h₁ : ∀ x : E, x ∈ S → τ x ∈ S) (h₂ : ∀ x : E, x ∈ S → τ.symm x ∈ S) (x : ↥S) :
    ((restrictEquiv S τ h₁ h₂ x : ↥S) : E) = τ x := rfl

theorem mem_maximalIdeal_iff {K : Type*} [Field K] (V : ValuationSubring K) {x : K} (hx : x ∈ V) :
    (⟨x, hx⟩ : ↥V) ∈ maximalIdeal ↥V ↔ x = 0 ∨ x⁻¹ ∉ V := by
  rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]

theorem not_isUnit_of_mem_maximalIdeal {K : Type*} [Field K] (S : Subring K) (V : ValuationSubring K) (h : ∀ x ∈ S, x ∈ V)
    {x : K} (hxS : x ∈ S) (hm : ∀ hxV : x ∈ V, (⟨x, hxV⟩ : ↥V) ∈ maximalIdeal ↥V) : ¬ IsUnit (⟨x, hxS⟩ : ↥S) := by
  intro hu
  let φ : ↥S →+* ↥V :=
    { toFun := fun y => ⟨y.1, h y.1 y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  have h1 : IsUnit (φ ⟨x, hxS⟩) := hu.map φ
  exact (IsLocalRing.mem_maximalIdeal _).mp (hm (h x hxS)) h1

theorem eq_of_trace (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    [Algebra ↥k₀ ↥(fieldBar q M')]
    (hsc : ∀ x : ↥k₀, algebraMap ↥k₀ ↥(fieldBar q M') x =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (x : AlgebraicClosure ℚ))
    (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M'))
    (hK1 : IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤)
    (W₀ : ValuationSubring ↥F₀)
    (hK2a : ∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀)
    (hK2b : IsDiscreteValuationRing ↥W₀)
    (hK2c : ∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)})
    (O O' : ValuationSubring ↥(fieldBar q M')) (hO : ∀ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ O ↔ f ∈ W₀)
    (hO' : ∀ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ O' ↔ f ∈ W₀) : O = O' := by
  let φ : AlgebraicClosure ℚ →ₐ[↥k₀] ↥(fieldBar q M') :=
    { (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) with commutes' := fun x => (hsc x).symm }
  have hφ : ∀ y, φ y = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') y := fun _ => rfl
  set L : IntermediateField ↥k₀ ↥(fieldBar q M') :=
    IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) with hLdef
  have hLeq : L = φ.fieldRange := by
    apply le_antisymm
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨y, rfl⟩
      rw [SetLike.mem_coe, AlgHom.mem_fieldRange]
      exact ⟨y, hφ y⟩
    · intro x hx
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
      rw [hφ]
      exact IntermediateField.subset_adjoin _ _ ⟨y, rfl⟩
  let ψ : AlgebraicClosure ℚ ≃ₐ[↥k₀] ↥L :=
    (AlgEquiv.ofInjectiveField φ).trans (IntermediateField.equivOfEq hLeq.symm)
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  haveI : Algebra.IsAlgebraic ↥k₀ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥k₀
  have hLalg : Algebra.IsAlgebraic ↥k₀ ↥L := ψ.isAlgebraic
  let AL : ValuationSubring ↥L := A.comap ψ.symm.toAlgHom.toRingHom
  have hmemAL : ∀ x : ↥L, x ∈ AL ↔ ψ.symm x ∈ A := fun x => Iff.rfl
  have hcomap : AL.comap (algebraMap ↥k₀ ↥L) = A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) := by
    ext x
    simp only [ValuationSubring.mem_comap]
    show ψ.symm (algebraMap ↥k₀ ↥L x) ∈ A ↔ _
    rw [AlgEquiv.commutes]
  have hπL : π₀ ∈ AL.comap (algebraMap ↥k₀ ↥L) := by rw [hcomap]; exact hπ
  have key : ∀ (X : ValuationSubring ↥k₀) (hX : π₀ ∈ X), X = A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) →
      IsDiscreteValuationRing ↥X ∧ maximalIdeal ↥X = Ideal.span {(⟨π₀, hX⟩ : ↥X)} ∧ HenselianLocalRing ↥X ∧
        IsAlgClosed (ResidueField ↥X) := by
    rintro X hX rfl
    exact ⟨hdvr, hunif, hhens, hres⟩
  obtain ⟨hdvr', hunif', hhens', hres'⟩ := key _ hπL hcomap
  obtain ⟨hint, htower⟩ := @ValuationSubring.isIntegral_and_exists_totallyRamified_layers_of_henselian
    ↥k₀ ↥(fieldBar q M') _ _ _ _ L hLalg AL π₀ hπL hdvr' hunif' hhens' hres'
  obtain ⟨hπW, hunifW⟩ := hK2c
  have hagree : ∀ x : ↥k₀, algebraMap ↥k₀ ↥L x ∈ AL ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀ := by
    intro x
    rw [hmemAL, AlgEquiv.commutes, ← hK2a]
    rfl
  exact ValuationSubring.eq_of_constantsTower_of_forall_mem_iff ↥k₀ ↥(fieldBar q M') L F₀ hK1 AL W₀ hagree
    hK2b π₀ hπW hunifW hint htower O O' hO hO'

theorem exists_levelAutBar_inv_eq (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 M' ∧ (levelAutBar q M' ζ γ)⁻¹ = levelAutBar q M' ζ γ' := by
  obtain ⟨G, -, hmem, hall⟩ := ModularCurve.FullLevel.exists_finite_subgroup_forall_levelAutBar_mem q M' hqM' ζ
  obtain ⟨γ', hγ', h⟩ := hall _ (G.inv_mem (hmem γ hγ))
  exact ⟨γ', hγ', h⟩

abbrev IsNodeTransport {K E k : Type*} [Field K] [Field E] [Algebra K E] [Field k] [Algebra k E]
    (F₀ : IntermediateField k E) (nodes : Finset (Subring ↥F₀)) (τ : E ≃ₐ[K] E) : Prop :=
  (∀ f : E, f ∈ F₀ → τ f ∈ F₀) ∧ (∀ f : E, f ∈ F₀ → τ.symm f ∈ F₀) ∧
  (∀ O ∈ nodes, ∃ O' ∈ nodes, ∀ (f : E) (hf : f ∈ F₀) (hf' : τ f ∈ F₀), (⟨f, hf⟩ : ↥F₀) ∈ O ↔ (⟨τ f, hf'⟩ : ↥F₀) ∈ O')

theorem isNodeTransport_one {K E k : Type*} [Field K] [Field E] [Algebra K E] [Field k] [Algebra k E]
    (F₀ : IntermediateField k E) (nodes : Finset (Subring ↥F₀)) : IsNodeTransport F₀ nodes (1 : E ≃ₐ[K] E) :=
  ⟨fun _ hf => hf, fun _ hf => hf, fun O hO => ⟨O, hO, fun _ _ _ => Iff.rfl⟩⟩

theorem isNodeTransport_mul {K E k : Type*} [Field K] [Field E] [Algebra K E] [Field k] [Algebra k E]
    (F₀ : IntermediateField k E) (nodes : Finset (Subring ↥F₀)) {τ₁ τ₂ : E ≃ₐ[K] E}
    (h₁ : IsNodeTransport F₀ nodes τ₁) (h₂ : IsNodeTransport F₀ nodes τ₂) : IsNodeTransport F₀ nodes (τ₁ * τ₂) := by
  obtain ⟨h1a, h1b, h1c⟩ := h₁
  obtain ⟨h2a, h2b, h2c⟩ := h₂
  refine ⟨fun f hf => h1a _ (h2a f hf), fun f hf => ?_, fun O hO => ?_⟩
  · rw [AlgEquiv.aut_mul, AlgEquiv.symm_trans_apply]; exact h2b _ (h1b f hf)
  · obtain ⟨O₂, hO₂, e₂⟩ := h2c O hO
    obtain ⟨O₁, hO₁, e₁⟩ := h1c O₂ hO₂
    refine ⟨O₁, hO₁, fun f hf hf' => ?_⟩
    rw [e₂ f hf (h2a f hf)]
    exact e₁ (τ₂ f) (h2a f hf) hf'

end EqvTransportBody
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_levelAut_transport_nodePlaces_igusaEnds_of_nodeCentre_igusaBranch.BranchTransportH1 P2MW.S_ModularCurve_FullLevel_levelAut_transport_nodePlaces_igusaEnds_of_nodeCentre_igusaBranch.EqvTransportBody"

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 51200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    {ι : Type} (K : ι → IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKfin : ∀ n, FiniteDimensional ↥k₀ ↥(K n))
    (An : ∀ n, ValuationSubring ↥(K n))
    (hAn : ∀ n (x : ↥(K n)), x ∈ An n ↔ (x : AlgebraicClosure ℚ) ∈ A)

    (n₀ : ι) (hn₀ : ∀ n, K n₀ ≤ K n)

    (hKcof : ∀ T : Finset (AlgebraicClosure ℚ), ∃ n : ι, ∀ x ∈ T, x ∈ Set.range (fun y : ↥(K n) => (y : AlgebraicClosure ℚ)))

    (πt : AlgebraicClosure ℚ) (hπt : πt ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπA : πt ∈ A)

    (htame : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter πt τ = 1 → ∀ x : ↥(K n₀), τ (x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))

    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKb : Kb = ⊥)
    (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) (hϖb0 : ϖb ≠ 0) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (

      (∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ∃ c : ↥k₀, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = ((c : ↥k₀) : AlgebraicClosure ℚ)) ∧

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) ∧

      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ γ f ∈ F₀) ∧

      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0)) →
    ∀ (W₀ : ValuationSubring ↥F₀),

    ∀ (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B)
      (hjR : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
         coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
         ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
      (hjs : (R₀.residue ⟨_, hjR⟩ : modularFunctionFieldC (ResidueField A) M') ∈
         (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring)
      (hJK : ModularCurve.jqNModC (AlgebraicClosure ℚ) q ∈ fieldBar q M')
      (a₀ : ↥k₀) (ha₀ : (a₀ : (AlgebraicClosure ℚ)) ∈ A)
      (hpin : (residue A ⟨(a₀ : (AlgebraicClosure ℚ)), ha₀⟩) ^ q =
         (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hjR⟩))
      (nodes : Finset (Subring ↥F₀)),
      (

      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) ∧
      IsDiscreteValuationRing ↥W₀ ∧
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)}) ∧

      (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
            (⟨_, hF⟩ : ↥F₀) ∈ W₀ ∧
            ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
              residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
              ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ W₀, (⟨_, hm⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) ∧

      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ γ f ∈ F₀),
          (⟨f, hf⟩ : ↥F₀) ∈ W₀ ↔ (⟨_, hf'⟩ : ↥F₀) ∈ W₀) ∧

      (

        (∀ a : ↥Ab, ((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥B, (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        @Algebra.FormallySmooth ↥Ab ↥B _ _ alg ∧ @Algebra.FinitePresentation ↥Ab ↥B _ _ alg ∧
        Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb}) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ W₀) ∧
        Prime (@algebraMap ↥Ab ↥B _ _ alg ϖb) ∧
        (∀ f : ↥F₀, f ∈ W₀ ↔ ∃ g h : ↥B, ¬ (@algebraMap ↥Ab ↥B _ _ alg ϖb ∣ h) ∧ (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ B) ∧
        (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ B → levelAutBar q M' ζ γ f ∈ B) ∧

        (∃ (b : ↥(fieldBar q M')) (hbF : b ∈ F₀), b ∈ B ∧ ∀ V : ValuationSubring ↥F₀,
          (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V) →
          (∀ hπV : algebraMap ↥k₀ ↥F₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
          ∀ (hjF : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)
            (hjV : (⟨(IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')), hjF⟩ : ↥F₀) ∈ V),
            (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
              ∀ hp : Polynomial.aeval (⟨(IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')), hjF⟩ : ↥F₀) (p.map (algebraMap ↥k₀ ↥F₀)) ∈ V,
                (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
          (⟨b, hbF⟩ : ↥F₀) ∉ V) ∧

        (∀ s' : ↥W, s' ≠ s → ∃ (b : ↥(fieldBar q M')) (hbF : b ∈ F₀), b ∈ B ∧ ∀ V : ValuationSubring ↥F₀,
          (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V) →
          (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
            (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                ((s' : ↥W) : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
              ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                (⟨_, hF⟩ : ↥F₀) ∈ V ∧
                ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
                  residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                    ((s' : ↥W) : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                  ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
          (⟨b, hbF⟩ : ↥F₀) ∉ V) ∧

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (ρ : ↥B →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            RingHom.ker ρ = Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb} ∧
            (∀ a : ↥Ab, ρ (@algebraMap ↥Ab ↥B _ _ alg a) =
              algebraMap (ResidueField ↥A) ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) (IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩)) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), ∃ g h : ↥B, ρ h ≠ 0 ∧ z * ρ h = ρ g) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), z ∈ Set.range ρ ↔
              (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈ Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q)
                (f : ↥B) (hf' : levelAutBar q M' ζ γ⁻¹ (f : ↥(fieldBar q M')) ∈ B),
                ((ρ ⟨_, hf'⟩ : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                  DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((ρ f : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧

        (
          nodes.card = q + 1 ∧

          (∃ Bc : Subring ↥F₀,
            (∃ T : Finset ↥F₀, Bc = Subring.closure
              ({f : ↥F₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥F₀ x} ∪ (↑T : Set ↥F₀))) ∧
            ∀ O ∈ nodes, (∀ f : ↥F₀, f ∈ Bc → f ∈ O) ∧
              (∀ f : ↥F₀, f ∈ O ↔ ∃ g h : ↥F₀, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) ∧

          (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ O ∈ nodes, ∃ O' ∈ nodes,
            ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ γ f ∈ F₀), (⟨f, hf⟩ : ↥F₀) ∈ O ↔ (⟨_, hf'⟩ : ↥F₀) ∈ O') ∧
          (∀ (ζ : Idx q), ∀ O ∈ nodes, ∀ O' ∈ nodes, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧
            ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ γ f ∈ F₀), (⟨f, hf⟩ : ↥F₀) ∈ O ↔ (⟨_, hf'⟩ : ↥F₀) ∈ O') ∧

          (∀ O ∈ nodes, ∀ O' ∈ nodes, O ≠ O' → ∃ (f : ↥F₀) (hf : f ∈ O) (hf' : f ∈ O'),
            ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) ∧

          (∀ V : ValuationSubring ↥F₀, (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V) →
                  (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
              (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
              (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                  ↥(modularFunctionFieldBar M'))) →
              (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                  (⟨_, hF⟩ : ↥F₀) ∈ V ∧
                  ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
                    residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                    ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ V) ∨
            (∃ O ∈ nodes, ∀ (f : ↥F₀) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))) ∧

          (∀ O ∈ nodes,

            (∀ f : ↥F₀, f ∈ O → f ∈ W₀) ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
            (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ O) ∧
            (∀ (f : ↥F₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥F₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) ∧

            (∃ (E₀ : ℕ) (_ : 1 ≤ E₀)

               (_ : ∃ v : ↥k₀, (v : (AlgebraicClosure ℚ)) ∈ A ∧ ((v⁻¹ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A ∧
                  π₀ ^ E₀ = ϖt ^ (2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) * v)
               (hπO : algebraMap ↥k₀ ↥F₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
               (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
               (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
              cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) ∧
              (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥F₀ x ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ∧
              ((cy : ↥F₀) ∈ W₀) ∧ (∀ hcy : (cy : ↥F₀) ∈ W₀, (⟨(cy : ↥F₀), hcy⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) ∧
              (∀ hcx : (cx : ↥F₀) ∈ W₀, (⟨(cx : ↥F₀), hcx⟩ : ↥W₀) ∉ maximalIdeal ↥W₀) ∧

              (∃ (hjF : (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                    algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a₀ : (AlgebraicClosure ℚ)) ∈ F₀)
                 (hjO : (⟨_, hjF⟩ : ↥F₀) ∈ O) (e : ℕ) (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ), 1 ≤ e ∧
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hjO⟩) =
                  (wV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) ^ e) ∧

              (∃ Wx : ValuationSubring ↥F₀,
                (∀ f : ↥F₀, f ∈ O → f ∈ Wx) ∧
                (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ Wx) ∧
                IsDiscreteValuationRing ↥Wx ∧
                (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) ∧
                (∃ t : ↥Wx, ∀ p : Polynomial ↥k₀, (∀ n, ((p.coeff n : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                  (∃ hm : Polynomial.aeval (t : ↥F₀) p ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ n, ∃ hc : algebraMap ↥k₀ ↥F₀ (p.coeff n) ∈ Wx, (⟨_, hc⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcx : (cx : ↥F₀) ∈ Wx, (⟨(cx : ↥F₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcy : (cy : ↥F₀) ∈ Wx, (⟨(cy : ↥F₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
                  (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
                  (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                      ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                      ↥(modularFunctionFieldBar M'))) →
                  ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                    (⟨_, hF⟩ : ↥F₀) ∈ Wx ∧
                    (∀ hW : (⟨_, hF⟩ : ↥F₀) ∈ Wx, (⟨_, hW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ↔
                      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) ∧
                    ((R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                      (⟨_, hF⟩ : ↥F₀) ∈ O ∧
                      ∀ (hO : (⟨_, hF⟩ : ↥F₀) ∈ O) (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) (hcO : algebraMap ↥k₀ ↥F₀ c ∈ O),
                        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                        ¬ IsUnit ((⟨_, hO⟩ : ↥O) - ⟨_, hcO⟩))) ∧

                (∀ O' ∈ nodes, O' ≠ O → ∃ f : ↥F₀, f ∈ O' ∧ f ∉ Wx)) ∧

              (∃ Bx : Subring ↥F₀,
                (∀ f : ↥F₀, f ∈ Bx → (f : ↥(fieldBar q M')) ∈ B ∧ f ∈ O) ∧
                (∀ (f : ↥F₀), f ∈ Bx → ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'),
                  0 ≤ P.ord ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M'))) → 0 ≤ P.ord (f : ↥(fieldBar q M'))) ∧
                (∀ f : ↥F₀, f ∈ O ↔ ∃ g h : ↥F₀, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧
                (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ Bx ∧ h ∈ Bx ∧ h ≠ 0 ∧ f * h = g) ∧
                (∃ T : Finset ↥F₀, Bx = Subring.closure
                  ({f : ↥F₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥F₀ x} ∪ (↑T : Set ↥F₀))) ∧

                (∃ b : ↥F₀, b ∈ Bx ∧ ∀ V : ValuationSubring ↥F₀,
                  (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V) →
                  (∀ hπV : algebraMap ↥k₀ ↥F₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  ∀ (hjF : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)
                    (hjV : (⟨(IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')), hjF⟩ : ↥F₀) ∈ V),
                    (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                      ∀ hp : Polynomial.aeval (⟨(IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')), hjF⟩ : ↥F₀) (p.map (algebraMap ↥k₀ ↥F₀)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                  (∃ f : ↥F₀, f ∈ O ∧ f ∉ V) → b ∉ V))))))
      ) →
      (∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
        (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) →

    ∀ (N : Finset (Place (ResidueField ↥A) FSS)) (Oof : Place (ResidueField ↥A) FSS → Subring ↥F₀),
      (∀ nd ∈ N, Oof nd ∈ nodes) → (∀ O ∈ nodes, ∃ nd ∈ N, Oof nd = O) → (∀ nd ∈ N, ∀ nd' ∈ N, Oof nd = Oof nd' → nd = nd') →
    ∀ (S : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
      (∀ nd ∈ N, ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S nd ↔
        (∀ f : ↥F₀, f ∈ Oof nd → (f : ↥(fieldBar q M')) ∈ P.toValuationSubring) ∧
        (∀ (f : ↥F₀) (hfO : f ∈ Oof nd), ¬ IsUnit (⟨f, hfO⟩ : ↥(Oof nd)) →
          ∃ h : P.evalAt (f : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A)) →
      (∀ nd ∈ N,
        (∀ (f : ↥F₀) (_ : f ∈ Oof nd) (hR : (f : ↥(fieldBar q M')) ∈ R.integers), R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ nd.toValuationSubring) ∧
        (∀ (f : ↥F₀) (hf : f ∈ Oof nd) (hR : (f : ↥(fieldBar q M')) ∈ R.integers), ¬ IsUnit (⟨f, hf⟩ : ↥(Oof nd)) →
          ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ nd.toValuationSubring,
            (⟨_, hm⟩ : ↥nd.toValuationSubring) ∈ maximalIdeal ↥nd.toValuationSubring) ∧
        (∀ y : Place (ResidueField ↥A) FSS,
          (∀ (f : ↥F₀) (_ : f ∈ Oof nd) (hR : (f : ↥(fieldBar q M')) ∈ R.integers), R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ y.toValuationSubring) →
          (∀ (f : ↥F₀) (hf : f ∈ Oof nd) (hR : (f : ↥(fieldBar q M')) ∈ R.integers), ¬ IsUnit (⟨f, hf⟩ : ↥(Oof nd)) →
            ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ y.toValuationSubring,
              (⟨_, hm⟩ : ↥y.toValuationSubring) ∈ maximalIdeal ↥y.toValuationSubring) →
          y = nd)) →
    ∀ (FIx : Place (ResidueField ↥A) FSS → Type) [∀ x, Field (FIx x)] [∀ x, Algebra (ResidueField ↥A) (FIx x)]
      (Rx : ∀ x : Place (ResidueField ↥A) FSS, RegularProlongation A ↥(fieldBar q M') (FIx x))
      (Wx : Place (ResidueField ↥A) FSS → ValuationSubring ↥F₀),
      (∀ nd ∈ N, ∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ (Rx nd).integers ↔ f ∈ Wx nd)) →
      (∀ nd ∈ N, ∀ f : ↥F₀, f ∈ Oof nd → f ∈ Wx nd) →
      (∀ nd ∈ N, ∀ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ Wx nd, (⟨_, hπW⟩ : ↥(Wx nd)) ∈ maximalIdeal ↥(Wx nd)) →
      (∀ nd ∈ N, ∃ cyO : ↥F₀, cyO ∈ Oof nd ∧ (∀ hcy : cyO ∈ Wx nd, (⟨cyO, hcy⟩ : ↥(Wx nd)) ∉ maximalIdeal ↥(Wx nd)) ∧

        (∀ h₂ : ((cyO : ↥F₀) : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨((cyO : ↥F₀) : ↥(fieldBar q M')), h₂⟩ = 0) ∧
        ∀ V : ValuationSubring ↥F₀, (∀ f : ↥F₀, f ∈ Oof nd → f ∈ V) →
          (∀ hπV : algebraMap ↥k₀ ↥F₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
          (∀ hcy : cyO ∈ V, (⟨cyO, hcy⟩ : ↥V) ∉ maximalIdeal ↥V) → ∀ f : ↥F₀, f ∈ Wx nd → f ∈ V) →

    (

          (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∃ τN : Place (ResidueField A) FSS → Place (ResidueField A) FSS,
            ∀ nd ∈ N, τN nd ∈ N ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), (levelAutBar q M' ζ' γ) • P ∈ S nd ↔ P ∈ S (τN nd)) ∧
              ((Rx nd).integers).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = (Rx (τN nd)).integers) ∧

          (∀ τ ∈ Subgroup.closure {τ : (fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] (fieldBar q M') |
                ∃ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ' γ},
            ∀ (hτ : ∀ f : fieldBar q M', τ f ∈ R.integers ↔ f ∈ R.integers), ∀ nd ∈ N,
              R.resAut τ hτ • nd ∈ N ∧
              AlgebraicCurve.RegularProlongation.smulDisc τ (S nd) = S (R.resAut τ hτ • nd)))) := by
  letI instAlg : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hF₀ W₀ B alg hjR hjs hJK a₀ ha₀ hpin nodes hW₀ FSS _ _ R hRW N Oof hN1 hN2 hN3 S hS hC FIx _ _ Rx Wx hRxWx hOW
    hπWx hcan
  obtain ⟨hCHAR, hK1, hSTAB, hLD⟩ := hF₀
  obtain ⟨hK2a, hK2b, hK2c, hK4, hK5W, hM1, hM0a, hM0b, hM4a, hM4b, hM4c, hM2a, hM2b, hM2c, hM5a, hM5b, hE1, hE3, hM3,
    hNcard, hNcommon, hNEQV, hNEQV2, hNSEP, hCOVER, hNode⟩ := hW₀
  classical
  have hsc : ∀ x : ↥k₀, algebraMap ↥k₀ ↥(fieldBar q M') x =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (x : AlgebraicClosure ℚ) := fun _ => rfl
  have hcoeπ : ((algebraMap ↥k₀ ↥F₀ π₀ : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (π₀ : AlgebraicClosure ℚ) := rfl

  haveI hdvrI : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := hdvr
  have hirr : Irreducible (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hunif
  have hπ₀ne : (algebraMap ↥k₀ ↥F₀ π₀ : ↥F₀) ≠ 0 := by
    intro h0
    have h1 : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (π₀ : AlgebraicClosure ℚ) = 0 := by
      rw [← hcoeπ, h0]; rfl
    rw [map_eq_zero] at h1
    exact hirr.ne_zero (Subtype.ext (Subtype.ext h1))
  obtain ⟨instDom, instDVR, instCpl, hirr', -, -⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
      ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨π₀, hπ⟩ hirr
  haveI := instDom
  haveI := instDVR
  haveI := instCpl
  have hϖ : maximalIdeal (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
      ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) =
      Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
        (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
          ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr'
  have hπW₀m : ∀ h : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, (⟨_, h⟩ : ↥W₀) ∈ maximalIdeal ↥W₀ := by
    obtain ⟨hπW, hW₀unif⟩ := hK2c
    intro h; rw [hW₀unif]; exact Ideal.mem_span_singleton_self _

  have nodePkg : ∀ O ∈ nodes,
      (∀ f : ↥F₀, f ∈ O → f ∈ W₀) ∧
      ∃ (D : ValuationSubring ↥F₀) (cy : ↥F₀),
        (∀ f : ↥F₀, f ∈ O → f ∈ D) ∧
        (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ D) ∧
        IsDiscreteValuationRing ↥D ∧
        (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ D, maximalIdeal ↥D = Ideal.span {(⟨_, hπW⟩ : ↥D)}) ∧
        cy ∈ O ∧ (∀ h : cy ∈ W₀, (⟨cy, h⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) ∧ (∀ h : cy ∈ D, (⟨cy, h⟩ : ↥D) ∉ maximalIdeal ↥D) ∧
        ∀ (e : ↥F₀ ≃+* ↥F₀) (O₀ : Subring ↥F₀), (∀ x : ↥F₀, x ∈ O₀ ↔ e x ∈ O) → (∀ x : ↥F₀, x ∈ W₀ ↔ e x ∈ W₀) →
          e (algebraMap ↥k₀ ↥F₀ π₀) = algebraMap ↥k₀ ↥F₀ π₀ →
          ∀ (Dd : ValuationSubring ↥F₀), (∀ x : ↥F₀, x ∈ O₀ → x ∈ Dd) →
            (∀ h : algebraMap ↥k₀ ↥F₀ π₀ ∈ Dd, (⟨_, h⟩ : ↥Dd) ∈ maximalIdeal ↥Dd) →
            ∀ (c : ↥F₀), c ∈ O₀ → (∀ h : c ∈ W₀, (⟨c, h⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) →
              (∀ h : c ∈ Dd, (⟨c, h⟩ : ↥Dd) ∉ maximalIdeal ↥Dd) →
              ∀ x : ↥F₀, x ∈ Dd ↔ e x ∈ D := by
    intro O hO
    obtain ⟨hOW₀, hloc, hnoeth, hOconst, hOres, E₀, hE₀, hmodulus, hπO, cx, cy, u, ι, γU, γV, hcxcy, hconst, hιcx, hιcy,
      hcyW₀, hcyW₀m, hcxW₀, hN7, ⟨D, hOD, hDconst, hDdvr, hDunif, hDtr, hcxD, hcyD, hDlaws, hIGSEP⟩,
      ⟨Bx, hBxBO, hBxreg, hOloc, hBxfrac, hBxfg, hN5⟩⟩ := hNode O hO
    haveI := hloc
    haveI := hnoeth
    refine ⟨hOW₀, D, (cy : ↥F₀), hOD, hDconst, hDdvr, hDunif, cy.2, hcyW₀m, hcyD, ?_⟩
    intro e O₀ hO₀ heW₀ hπe Dd hODd hπDd c hcO₀ hcW₀ hcDd
    obtain ⟨hπD, hDunif'⟩ := hDunif
    have hπDm : ∀ h : algebraMap ↥k₀ ↥F₀ π₀ ∈ D, (⟨_, h⟩ : ↥D) ∈ maximalIdeal ↥D := fun h => by
      rw [hDunif']; exact Ideal.mem_span_singleton_self _
    have hfrac : ∀ x : ↥F₀, ∃ r s : ↥F₀, r ∈ O ∧ s ∈ O ∧ s ≠ 0 ∧ x * s = r := fun x => by
      obtain ⟨g, h, hg, hh, h0, hx⟩ := hBxfrac x
      exact ⟨g, h, (hBxBO g hg).2, (hBxBO h hh).2, h0, hx⟩
    exact EqvTransportBody.branchTransport ↥F₀ e O₀ O hO₀
      W₀ (fun x hx => (heW₀ x).mpr (hOW₀ _ ((hO₀ x).mp hx))) hOW₀ heW₀
      (algebraMap ↥k₀ ↥F₀ π₀) hπ₀ne ((hO₀ _).mpr (by rw [hπe]; exact hπO)) hπO hπe hπW₀m
      (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
        (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
          ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩)
      hϖ E₀ hE₀ ι (hconst π₀ hπ hπO) hfrac
      (cx : ↥F₀) cx.2 hcxW₀
      Dd D hODd hOD hπDd hπDm hDdvr hcxD
      c hcO₀ hcW₀ hcDd (cy : ↥F₀) cy.2 hcyW₀m hcyD

  have cyOfacts : ∀ nd₀ ∈ N, ∃ cyO : ↥F₀, cyO ∈ Oof nd₀ ∧ (∀ h : cyO ∈ W₀, (⟨cyO, h⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) ∧
      (∀ h : cyO ∈ Wx nd₀, (⟨cyO, h⟩ : ↥(Wx nd₀)) ∉ maximalIdeal ↥(Wx nd₀)) := by
    intro nd₀ hnd₀
    obtain ⟨cyO, hcyOO, hcyOWx, hres0, -⟩ := hcan nd₀ hnd₀
    refine ⟨cyO, hcyOO, fun h => ?_, hcyOWx⟩
    have hR : ((cyO : ↥F₀) : ↥(fieldBar q M')) ∈ R.integers := (hRW cyO).mpr h
    have hker : (⟨_, hR⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers := by
      rw [← R.ker_residue, RingHom.mem_ker]; exact hres0 hR
    rw [EqvTransportBody.mem_maximalIdeal_iff] at hker ⊢
    rcases hker with h0 | hinv
    · left; exact_mod_cast h0
    · right; intro hinvW
      exact hinv ((hRW cyO⁻¹).mpr hinvW)

  have hPlev : ∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      EqvTransportBody.IsNodeTransport F₀ nodes (levelAutBar q M' ζ γ) := by
    intro ζ γ hγ
    obtain ⟨γ', hγ', hinv⟩ := EqvTransportBody.exists_levelAutBar_inv_eq q M' hqM' ζ γ hγ
    refine ⟨fun f hf => hSTAB ζ γ hγ f hf, fun f hf => ?_, fun O hO => hNEQV ζ γ hγ O hO⟩
    rw [← AlgEquiv.aut_inv, hinv]; exact hSTAB ζ γ' hγ' f hf
  have hPclosure : ∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
      ∃ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ' γ},
      EqvTransportBody.IsNodeTransport F₀ nodes τ := by
    intro τ hτ
    refine Subgroup.closure_induction'' (p := fun τ _ => EqvTransportBody.IsNodeTransport F₀ nodes τ) ?_ ?_
      (EqvTransportBody.isNodeTransport_one F₀ nodes)
      (fun x y _ _ hx hy => EqvTransportBody.isNodeTransport_mul F₀ nodes hx hy) hτ
    · rintro x ⟨ζ', γ, hγ, rfl⟩; exact hPlev ζ' γ hγ
    · rintro x ⟨ζ', γ, hγ, rfl⟩
      obtain ⟨γ', hγ', hinv⟩ := EqvTransportBody.exists_levelAutBar_inv_eq q M' hqM' ζ' γ hγ
      rw [hinv]; exact hPlev ζ' γ' hγ'

  have transportS : ∀ (τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M'))
      (hP : EqvTransportBody.IsNodeTransport F₀ nodes τ), ∀ nd ∈ N, ∀ nd' ∈ N,
      (∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : τ f ∈ F₀), (⟨f, hf⟩ : ↥F₀) ∈ Oof nd ↔ (⟨τ f, hf'⟩ : ↥F₀) ∈ Oof nd') →
      AlgebraicCurve.RegularProlongation.smulDisc τ (S nd) = S nd' ∧
      ∀ hτ : (∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers), R.resAut τ hτ • nd = nd' := by
    intro τ hP nd hnd nd' hnd' hOO'
    let τ₀ : ↥F₀ ≃+* ↥F₀ := EqvTransportBody.restrictEquiv F₀ τ.toRingEquiv hP.1 hP.2.1
    have H := EqvTransportBody.nodeDataTransport A τ
      (algebraMap ↥F₀ ↥(fieldBar q M')) τ₀ (fun x => rfl) (Oof nd) (Oof nd') (fun x => hOO' x x.2 (hP.1 _ x.2))
      (S nd) (S nd') (hS nd hnd) (hS nd' hnd')
    exact ⟨H.1, fun hτ => H.2 FSS R hτ nd nd' (hC nd hnd).1 (hC nd hnd).2.1 (hC nd' hnd').2.2⟩
  refine ⟨?_, ?_⟩
  ·
    intro ζ' γ hγ
    obtain ⟨γ', hγ', hσinv⟩ := EqvTransportBody.exists_levelAutBar_inv_eq q M' hqM' ζ' γ hγ
    have hPσ : EqvTransportBody.IsNodeTransport F₀ nodes (levelAutBar q M' ζ' γ) := hPlev ζ' γ hγ
    have hPσi : EqvTransportBody.IsNodeTransport F₀ nodes (levelAutBar q M' ζ' γ)⁻¹ := by
      rw [hσinv]; exact hPlev ζ' γ' hγ'
    have hchoice : ∀ nd ∈ N, ∃ nd' ∈ N, ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : (levelAutBar q M' ζ' γ)⁻¹ f ∈ F₀),
        (⟨f, hf⟩ : ↥F₀) ∈ Oof nd ↔ (⟨_, hf'⟩ : ↥F₀) ∈ Oof nd' := by
      intro nd hnd
      obtain ⟨O', hO', hOO'⟩ := hPσi.2.2 (Oof nd) (hN1 nd hnd)
      obtain ⟨nd', hnd', heq⟩ := hN2 O' hO'
      exact ⟨nd', hnd', by rw [heq]; exact hOO'⟩
    have hchoice' : ∀ nd : Place (ResidueField ↥A) FSS, ∃ nd' : Place (ResidueField ↥A) FSS, nd ∈ N → (nd' ∈ N ∧
        ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : (levelAutBar q M' ζ' γ)⁻¹ f ∈ F₀),
          (⟨f, hf⟩ : ↥F₀) ∈ Oof nd ↔ (⟨_, hf'⟩ : ↥F₀) ∈ Oof nd') := by
      intro nd
      by_cases h : nd ∈ N
      · obtain ⟨nd', h1, h2⟩ := hchoice nd h
        exact ⟨nd', fun _ => ⟨h1, h2⟩⟩
      · exact ⟨nd, fun h' => absurd h' h⟩
    choose τN hτN using hchoice'
    refine ⟨τN, ?_⟩
    intro nd hnd
    obtain ⟨hnd', hOO'⟩ := hτN nd hnd
    refine ⟨hnd', ?_, ?_⟩
    ·
      obtain ⟨hS', -⟩ := transportS _ hPσi nd hnd (τN nd) hnd' hOO'
      intro P
      rw [← hS', AlgebraicCurve.RegularProlongation.mem_smulDisc_iff, inv_inv]
    ·
      obtain ⟨hO₁W₀, D₁, cy₁, hO₁D₁, hD₁const, hD₁dvr, hD₁unif, hcy₁O, hcy₁W₀, hcy₁D₁, htr₁⟩ := nodePkg _ (hN1 nd hnd)
      obtain ⟨hO₂W₀, D₂, cy₂, hO₂D₂, hD₂const, hD₂dvr, hD₂unif, hcy₂O, hcy₂W₀, hcy₂D₂, htr₂⟩ := nodePkg _ (hN1 (τN nd) hnd')
      have hπD₂m : ∀ h : algebraMap ↥k₀ ↥F₀ π₀ ∈ D₂, (⟨_, h⟩ : ↥D₂) ∈ maximalIdeal ↥D₂ := fun h => by
        obtain ⟨h', hu⟩ := hD₂unif; rw [hu]; exact Ideal.mem_span_singleton_self _

      have hid₁ : ∀ x : ↥F₀, x ∈ Wx nd ↔ x ∈ D₁ := by
        obtain ⟨cyO, hcyOO, hcyOW₀, hcyOWx⟩ := cyOfacts nd hnd
        exact htr₁ (RingEquiv.refl _) (Oof nd) (fun x => Iff.rfl) (fun x => Iff.rfl) rfl (Wx nd) (hOW nd hnd) (hπWx nd hnd)
          cyO hcyOO hcyOW₀ hcyOWx
      have hid₂ : ∀ x : ↥F₀, x ∈ Wx (τN nd) ↔ x ∈ D₂ := by
        obtain ⟨cyO, hcyOO, hcyOW₀, hcyOWx⟩ := cyOfacts (τN nd) hnd'
        exact htr₂ (RingEquiv.refl _) (Oof (τN nd)) (fun x => Iff.rfl) (fun x => Iff.rfl) rfl (Wx (τN nd)) (hOW (τN nd) hnd')
          (hπWx (τN nd) hnd') cyO hcyOO hcyOW₀ hcyOWx

      let e : ↥F₀ ≃+* ↥F₀ := EqvTransportBody.restrictEquiv F₀ (levelAutBar q M' ζ' γ).toRingEquiv hPσ.1 hPσ.2.1
      have hecoe : ∀ x : ↥F₀, ((e x : ↥F₀) : ↥(fieldBar q M')) = levelAutBar q M' ζ' γ x := fun _ => rfl
      have heO : ∀ x : ↥F₀, x ∈ Oof (τN nd) ↔ e x ∈ Oof nd := by
        intro x
        have hx' : (levelAutBar q M' ζ' γ)⁻¹ ((levelAutBar q M' ζ' γ) x) ∈ F₀ := by
          rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]; exact x.2
        have h := hOO' ((levelAutBar q M' ζ' γ) x) (hPσ.1 _ x.2) hx'
        have hxeq : (⟨(levelAutBar q M' ζ' γ)⁻¹ ((levelAutBar q M' ζ' γ) x), hx'⟩ : ↥F₀) = x :=
          Subtype.ext (show (levelAutBar q M' ζ' γ)⁻¹ ((levelAutBar q M' ζ' γ) (x : ↥(fieldBar q M'))) = x by
            rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply])
        have h2 : (⟨(levelAutBar q M' ζ' γ)⁻¹ ((levelAutBar q M' ζ' γ) x), hx'⟩ : ↥F₀) ∈ Oof (τN nd) ↔ x ∈ Oof (τN nd) := by
          rw [hxeq]
        exact (h.trans h2).symm
      have heW₀ : ∀ x : ↥F₀, x ∈ W₀ ↔ e x ∈ W₀ := fun x => hK5W ζ' γ hγ x x.2 (hPσ.1 _ x.2)
      have hπe : e (algebraMap ↥k₀ ↥F₀ π₀) = algebraMap ↥k₀ ↥F₀ π₀ := by
        apply Subtype.ext
        rw [hecoe, hcoeπ]
        exact (levelAutBar q M' ζ' γ).commutes (π₀ : AlgebraicClosure ℚ)
      have htrans : ∀ x : ↥F₀, x ∈ D₂ ↔ e x ∈ D₁ :=
        htr₁ e (Oof (τN nd)) heO heW₀ hπe D₂ hO₂D₂ hπD₂m cy₂ hcy₂O hcy₂W₀ hcy₂D₂

      have hW : ∀ f : ↥F₀, (f : ↥(fieldBar q M')) ∈
          ((Rx nd).integers).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom ↔ f ∈ D₂ := by
        intro f
        rw [ValuationSubring.mem_comap, htrans f, ← hid₁ (e f), ← hRxWx nd hnd (e f)]
        exact Iff.rfl
      have hW' : ∀ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ (Rx (τN nd)).integers ↔ f ∈ D₂ :=
        fun f => (hRxWx (τN nd) hnd' f).trans (hid₂ f)
      exact EqvTransportBody.eq_of_trace q M' A k₀ π₀ hπ hdvr hunif hhens hres hsc F₀ hK1 D₂ hD₂const hD₂dvr hD₂unif
        _ _ hW hW'
  ·
    intro τ hτmem hτ nd hnd
    obtain ⟨O', hO', hOO'⟩ := (hPclosure τ hτmem).2.2 (Oof nd) (hN1 nd hnd)
    obtain ⟨nd', hnd', heq⟩ := hN2 O' hO'
    obtain ⟨hS', hcen⟩ := transportS τ (hPclosure τ hτmem) nd hnd nd' hnd' (by rw [heq]; exact hOO')
    rw [hcen hτ]
    exact ⟨hnd', hS'⟩

end S_ModularCurve_FullLevel_levelAut_transport_nodePlaces_igusaEnds_of_nodeCentre_igusaBranch
end P2MW
export P2MW.S_ModularCurve_FullLevel_levelAut_transport_nodePlaces_igusaEnds_of_nodeCentre_igusaBranch (solution)
