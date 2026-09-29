-- Prove2me | solution 1 for ModularCurve.exists_elliptic_cycSub_orbitMap_prime_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/493dd81c-8b51-58b3-992d-440731682890

import Definitions.Def_ModularCurve_TatePoint
import Definitions.Def_ModularCurve_EMD
import Definitions.Def_HahnSeries_Monodromy
import Definitions.Def_ModularCurve_SpecialisationBridge
import Definitions.Def_ModularCurve_CycSubRootBridge
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Theorems.Thm_ModularCurve_exists_place_of_emb
import Theorems.Thm_ModularCurve_samePlace_iff_exists_monodromy
import Theorems.Thm_ModularCurve_natCard_normalized_algHom_jBar_eq_toNat_ord
import Theorems.Thm_ModularCurve_place_eq_of_induces
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_WeierstrassCurve_exists_isElliptic_map_veluQuotient_j
import Theorems.Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_transcendental
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.SetTheory.Cardinal.Finite
import Theorems.Thm_ModularCurve_exists_emb_equiv_rootsAt
import Theorems.Thm_ModularCurve_B3_b3_specialisationEquivariance
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_elliptic_cycSub_orbitMap_prime_of_ne_two
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

noncomputable section

open scoped Classical

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_elliptic_cycSub_orbitMap_prime_of_ne_two.ModularCurve ModularCurve.TatePoint AlgebraicCurve WeierstrassCurve Polynomial"

attribute [local instance] ModularCurve.TatePoint.isAlgClosed_H ModularCurve.TatePoint.charZero_H

namespace ModularCurve
p2m_export "ModularCurve" "ModularPolynomialData Emb Induces SamePlace CycSub SameOrbit EMD jBar jpBar modularFunctionFieldBar B3.nearCurve_map_of_mem_monodromy B3.nearTransport B3.nearTransport_some B3.b3Act B3.b3Act_zmultiples TatePoint.isAlgClosed_H TatePoint.charZero_H exists_place_of_emb samePlace_iff_exists_monodromy natCard_normalized_algHom_jBar_eq_toNat_ord place_eq_of_induces exists_modularPolynomialData_evalSymm exists_emb_equiv_rootsAt B3.b3_specialisationEquivariance"
namespace WiringB2
p2m_open "ModularCurve"

private theorem algebraMap_eq_C (r : Qbar) :
    algebraMap Qbar H r = HahnSeries.C r := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

theorem map_jNear {j₀ : Qbar} {m : H ≃ₐ[Qbar] H} (hm : m ∈ HahnSeries.monodromy Qbar) :
    m (jNear j₀) = jNear j₀ := by
  rw [jNear, map_add, ← algebraMap_eq_C, AlgEquiv.commutes, algebraMap_eq_C,
    HahnSeries.fixes_single_one_of_mem_monodromy hm]

def twistEmb {p : ℕ} [NeZero p] {j₀ : Qbar} (m : HahnSeries.monodromy Qbar) (ψ : Emb p j₀) :
    Emb p j₀ :=
  ⟨((m : H ≃ₐ[Qbar] H).toAlgHom.comp ψ.1 : _ →ₐ[Qbar] H), by
    have h := ψ.2
    simp only [AlgHom.comp_apply]
    rw [show ψ.1 (jBar p) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : Qbar) from h]
    exact map_jNear m.2⟩

def twistRoot {p : ℕ} [NeZero p] (data : ModularPolynomialData p) (j₀ : Qbar)
    (m : HahnSeries.monodromy Qbar) (r : RootsAt data (nearCurve j₀).j) :
    RootsAt data (nearCurve j₀).j :=
  ⟨(m : H ≃ₐ[Qbar] H) r.1, by
    have hfix : (m : H ≃ₐ[Qbar] H) (nearCurve j₀).j = (nearCurve j₀).j := by
      rw [nearCurve_j]; exact map_jNear m.2
    have hcomp : (((m : H ≃ₐ[Qbar] H) : H →+* H)).comp
        (Polynomial.eval₂RingHom (Int.castRingHom H) (nearCurve j₀).j) =
        Polynomial.eval₂RingHom (Int.castRingHom H) (nearCurve j₀).j := by
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · simp
      · simpa using hfix
    have h := r.2.map (f := ((m : H ≃ₐ[Qbar] H) : H →+* H))
    rwa [Polynomial.map_map, hcomp] at h⟩

theorem samePlace_iff_twistEmb {p : ℕ} [NeZero p] {j₀ : Qbar} (ψ ψ' : Emb p j₀) :
    SamePlace ψ.1 ψ'.1 ↔ ∃ m : HahnSeries.monodromy Qbar, twistEmb m ψ = ψ' := by
  rw [ModularCurve.samePlace_iff_exists_monodromy p j₀ ψ ψ']
  constructor
  · rintro ⟨m, hm, hcomp⟩
    exact ⟨⟨m, hm⟩, Subtype.ext hcomp⟩
  · rintro ⟨m, hm⟩
    exact ⟨m.1, m.2, congrArg Subtype.val hm⟩

theorem emd_of_alpha (p : ℕ) [NeZero p] (data : ModularPolynomialData p)
    (j₀ : Qbar)
    (hB1 : {e : Emb p j₀ ≃ RootsAt data (nearCurve j₀).j //
      ∀ ψ : Emb p j₀, (e ψ).1 = ψ.1 (jpBar p)})
    (dict : RootsAt data (nearCurve j₀).j ≃ CycSubH (nearCurve j₀) p)
    (hdict : ∀ r : RootsAt data (nearCurve j₀).j, ∃ S : Finset (H × H),
      (nearCurve j₀).IsOddVeluSet S ∧
      (∀ P ∈ S, ∃ h : (nearCurve j₀).toAffine.Nonsingular P.1 P.2,
        WeierstrassCurve.Affine.Point.some P.1 P.2 h ∈ (dict r).1) ∧
      ∃ hQ : ((nearCurve j₀).veluQuotient S).IsElliptic,
        @WeierstrassCurve.j H _ ((nearCurve j₀).veluQuotient S) hQ = r.1)
    (act : HahnSeries.monodromy Qbar → (AddSubgroup (nearCurve j₀).toAffine.Point ≃
      AddSubgroup (nearCurve j₀).toAffine.Point))
    (hequiv : ∀ (m : HahnSeries.monodromy Qbar) (r : RootsAt data (nearCurve j₀).j),
      act m (dict r).1 = (dict (twistRoot data j₀ m r)).1)
    (hB3 : ∃ β : CycSubH (nearCurve j₀) p ≃ CycSub (WeierstrassCurve.ofJ j₀) p,
      ∀ G G' : CycSubH (nearCurve j₀) p,
        (∃ m : HahnSeries.monodromy Qbar, act m G.1 = G'.1) ↔
          SameOrbit (WeierstrassCurve.ofJ j₀) (β G).1 (β G').1) :
    EMD p j₀ := by
  have _hpin := hdict
  obtain ⟨e, he⟩ := hB1
  obtain ⟨β, hβ⟩ := hB3
  have hcarry : ∀ (m : HahnSeries.monodromy Qbar) (ψ : Emb p j₀),
      e (twistEmb m ψ) = twistRoot data j₀ m (e ψ) := fun m ψ =>
    Subtype.ext (show (e (twistEmb m ψ)).1 = (m : H ≃ₐ[Qbar] H) ((e ψ).1) from by
      rw [he (twistEmb m ψ), he ψ]; rfl)
  refine ⟨WeierstrassCurve.ofJ j₀, inferInstance, WeierstrassCurve.ofJ_j j₀,
    (e.trans dict).trans β, fun ψ ψ' => ?_⟩
  rw [samePlace_iff_twistEmb ψ ψ']
  simp only [Equiv.trans_apply]
  refine Iff.trans ?_ (hβ (dict (e ψ)) (dict (e ψ')))
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hequiv m (e ψ), ← hcarry m ψ, hm]⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, e.injective (dict.injective (Subtype.ext ?_))⟩
    rw [hcarry m ψ, ← hequiv m (e ψ)]
    exact hm

end ModularCurve.WiringB2

namespace ModularCurve p2m_export "ModularCurve" "ModularPolynomialData Emb Induces SamePlace CycSub SameOrbit EMD jBar jpBar modularFunctionFieldBar B3.nearCurve_map_of_mem_monodromy B3.nearTransport B3.nearTransport_some B3.b3Act B3.b3Act_zmultiples TatePoint.isAlgClosed_H TatePoint.charZero_H exists_place_of_emb samePlace_iff_exists_monodromy natCard_normalized_algHom_jBar_eq_toNat_ord place_eq_of_induces exists_modularPolynomialData_evalSymm exists_emb_equiv_rootsAt B3.b3_specialisationEquivariance" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.hbeta_of_emd_docks (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ)

    (hEP : ∀ ψ : {ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ) //
        ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)},
      ∃ (w : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) (g : ℚ),
        0 < g ∧ ∀ x : ↥(modularFunctionFieldBar N), (w.ord x : ℚ) * g = (ψ.1 x).order)

    (hPEO : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) →
      Nat.card {ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ) //
        ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ) ∧
        ∃ g : ℚ, 0 < g ∧ ∀ x, (w.ord x : ℚ) * g = (ψ x).order} =
      (w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat)

    (hC535 : ∀ {ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ)}
      {w w' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)},
      Induces ψ w → Induces ψ w' → w = w')

    (h : EMD N j₀) :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      ∃ f : CycSub E₀ N →
          {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
        (∀ H H' : CycSub E₀ N, f H = f H' ↔ SameOrbit E₀ H.1 H'.1) ∧
        ∀ w : {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
          ((w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).ord
              (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat =
            Nat.card {H : CycSub E₀ N // f H = w} := by
  classical
  obtain ⟨E₀, hell, hj, Φ, hiff⟩ := h

  have hInd : ∀ ψ : Emb N j₀,
      ∃ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), Induces ψ.1 w := by
    intro ψ
    obtain ⟨w, g, hg, hx⟩ := hEP ψ
    exact ⟨w, g, hg, hx⟩
  choose wOf hwOf using hInd

  have hwOf_eq : ∀ (ψ : Emb N j₀) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      Induces ψ.1 w → wOf ψ = w := fun ψ w hw => hC535 (hwOf ψ) hw

  have hC : ∀ c : AlgebraicClosure ℚ,
      algebraMap (AlgebraicClosure ℚ) (HahnSeries ℚ (AlgebraicClosure ℚ)) c = HahnSeries.C c := by
    intro c
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

  have habove : ∀ ψ : Emb N j₀, 0 < (wOf ψ).ord
      (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) := by
    intro ψ
    obtain ⟨g, hg, hx⟩ := hwOf ψ
    have h1 := hx (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)
    have himg : ψ.1 (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) =
        HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ) := by
      rw [map_sub, ψ.2, AlgHom.commutes, hC]
      ring
    rw [himg, HahnSeries.order_single one_ne_zero] at h1
    have hgne : g ≠ 0 := ne_of_gt hg
    have h2 : ((wOf ψ).ord
        (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) : ℚ) = 1 / g :=
      (eq_div_iff hgne).mpr h1
    have h3 : (0 : ℚ) < ((wOf ψ).ord
        (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) : ℚ) := by
      rw [h2]
      exact div_pos one_pos hg
    exact_mod_cast h3

  let f : CycSub E₀ N → {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
      0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)} :=
    fun H => ⟨wOf (Φ.symm H), habove (Φ.symm H)⟩
  have hf : ∀ H, (f H : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) = wOf (Φ.symm H) :=
    fun H => rfl
  refine ⟨E₀, hell, hj, f, fun H H' => ?_, fun w => ?_⟩
  ·
    have key := hiff (Φ.symm H) (Φ.symm H')
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at key
    rw [← key]
    constructor
    · intro hHH
      have hw : wOf (Φ.symm H) = wOf (Φ.symm H') := by
        have := congrArg Subtype.val hHH
        simpa [hf] using this
      exact ⟨wOf (Φ.symm H), hwOf _, hw ▸ hwOf _⟩
    · rintro ⟨w, hw, hw'⟩
      apply Subtype.ext
      rw [hf, hf, hwOf_eq _ w hw, hwOf_eq _ w hw']
  ·
    have hw := w.2

    let e1 : {H : CycSub E₀ N // f H = w} ≃ {ψ : Emb N j₀ // Induces ψ.1 w.1} :=
      { toFun := fun H => ⟨Φ.symm H.1, by
          have hH : wOf (Φ.symm H.1) = w.1 := by
            have := congrArg Subtype.val H.2
            simpa [hf] using this
          exact hH ▸ hwOf _⟩
        invFun := fun ψ => ⟨Φ ψ.1, by
          apply Subtype.ext
          rw [hf, Equiv.symm_apply_apply, hwOf_eq _ _ ψ.2]⟩
        left_inv := fun H => by
          apply Subtype.ext
          simp
        right_inv := fun ψ => by
          apply Subtype.ext
          simp }

    let e2 : {ψ : Emb N j₀ // Induces ψ.1 w.1} ≃
        {ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] HahnSeries ℚ (AlgebraicClosure ℚ) //
          ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ) ∧
          ∃ g : ℚ, 0 < g ∧ ∀ x, (w.1.ord x : ℚ) * g = (ψ x).order} :=
      Equiv.subtypeSubtypeEquivSubtypeInter
        (fun ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ]
            HahnSeries ℚ (AlgebraicClosure ℚ) =>
          ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ))
        (fun ψ => ∃ g : ℚ, 0 < g ∧ ∀ x, (w.1.ord x : ℚ) * g = (ψ x).order)
    rw [Nat.card_congr (e1.trans e2), hPEO w.1 hw]

private def embEquivRootsNear (p : ℕ) [NeZero p] (data : ModularPolynomialData p)
    (j₀ : Qbar) :
    {e : Emb p j₀ ≃ RootsAt data (nearCurve j₀).j //
      ∀ ψ : Emb p j₀, (e ψ).1 = ψ.1 (jpBar p)} := by
  have h := ModularCurve.exists_emb_equiv_rootsAt p data j₀
  rw [show jNear j₀ = (nearCurve j₀).j from (nearCurve_j j₀).symm] at h
  exact ⟨h.choose, h.choose_spec⟩

namespace ModularCurve
p2m_export "ModularCurve" "ModularPolynomialData Emb Induces SamePlace CycSub SameOrbit EMD jBar jpBar modularFunctionFieldBar B3.nearCurve_map_of_mem_monodromy B3.nearTransport B3.nearTransport_some B3.b3Act B3.b3Act_zmultiples TatePoint.isAlgClosed_H TatePoint.charZero_H exists_place_of_emb samePlace_iff_exists_monodromy natCard_normalized_algHom_jBar_eq_toNat_ord place_eq_of_induces exists_modularPolynomialData_evalSymm exists_emb_equiv_rootsAt B3.b3_specialisationEquivariance"
namespace HequivDev
p2m_open "ModularCurve"

private theorem j_congr {V V' : WeierstrassCurve H} (h : V = V')
    (hV : V.IsElliptic) (hV' : V'.IsElliptic) :
    @WeierstrassCurve.j H _ V hV = @WeierstrassCurve.j H _ V' hV' := by
  subst h; rfl

private theorem coordsOrZero_nearTransport (j₀ : Qbar) (m : HahnSeries.monodromy Qbar)
    (P : (nearCurve j₀).toAffine.Point) :
    (B3.nearTransport j₀ m P).coordsOrZero =
      Prod.map ((m : H ≃ₐ[Qbar] H) : H →+* H) ((m : H ≃ₐ[Qbar] H) : H →+* H)
        P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · have h0 : B3.nearTransport j₀ m (Affine.Point.zero) = Affine.Point.zero :=
      map_zero (B3.nearTransport j₀ m)
    rw [h0, Affine.Point.coordsOrZero_zero]
    ext <;> simp
  · rw [B3.nearTransport_some]
    rfl

private theorem oddOrderSummingSet_nearTransport (j₀ : Qbar) (m : HahnSeries.monodromy Qbar)
    (g : (nearCurve j₀).toAffine.Point) (n : ℕ) :
    (nearCurve j₀).oddOrderSummingSet (B3.nearTransport j₀ m g) n =
      ((nearCurve j₀).oddOrderSummingSet g n).image
        (Prod.map ((m : H ≃ₐ[Qbar] H) : H →+* H) ((m : H ≃ₐ[Qbar] H) : H →+* H)) := by
  simp only [WeierstrassCurve.oddOrderSummingSet, Finset.image_image]
  congr 1
  funext k
  rw [Function.comp_apply, ← coordsOrZero_nearTransport, map_nsmul]

private theorem addOrderOf_nearTransport (j₀ : Qbar) (m : HahnSeries.monodromy Qbar)
    (P : (nearCurve j₀).toAffine.Point) :
    addOrderOf (B3.nearTransport j₀ m P) = addOrderOf P :=
  addOrderOf_injective (B3.nearTransport j₀ m).toAddMonoidHom
    (B3.nearTransport j₀ m).injective P

private theorem j_quot_transport (j₀ : Qbar) (m : HahnSeries.monodromy Qbar)
    (Q : (nearCurve j₀).toAffine.Point) (n : ℕ)
    (hQel : ((nearCurve j₀).veluQuotient ((nearCurve j₀).oddOrderSummingSet Q n)).IsElliptic)
    (hQel' : ((nearCurve j₀).veluQuotient
      ((nearCurve j₀).oddOrderSummingSet (B3.nearTransport j₀ m Q) n)).IsElliptic) :
    @WeierstrassCurve.j H _ _ hQel' =
      (m : H ≃ₐ[Qbar] H) (@WeierstrassCurve.j H _ _ hQel) := by
  obtain ⟨hQmap, hj⟩ := WeierstrassCurve.exists_isElliptic_map_veluQuotient_j (nearCurve j₀)
    (((m : H ≃ₐ[Qbar] H) : H →+* H)) ((nearCurve j₀).oddOrderSummingSet Q n) hQel
  have hcurve : (nearCurve j₀).veluQuotient
      ((nearCurve j₀).oddOrderSummingSet (B3.nearTransport j₀ m Q) n) =
      ((nearCurve j₀).map (((m : H ≃ₐ[Qbar] H) : H →+* H))).veluQuotient
        (((nearCurve j₀).oddOrderSummingSet Q n).image
          (Prod.map ((m : H ≃ₐ[Qbar] H) : H →+* H) ((m : H ≃ₐ[Qbar] H) : H →+* H))) := by
    rw [oddOrderSummingSet_nearTransport, B3.nearCurve_map_of_mem_monodromy j₀ m.2]
  exact (j_congr hcurve hQel' hQmap).trans hj

end ModularCurve.HequivDev

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.hequiv_rootsEquivCycSubH (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (j₀ : Qbar) (data : ModularPolynomialData p)
    (m : HahnSeries.monodromy Qbar) (r : RootsAt data (nearCurve j₀).j) :
    (AddEquiv.mapAddSubgroup (B3.nearTransport j₀ m)).toEquiv
        (rootsEquivCycSubH (nearCurve j₀) hp2 data (nearCurve_j_transcendental j₀) r).1 =
      (rootsEquivCycSubH (nearCurve j₀) hp2 data (nearCurve_j_transcendental j₀)
          (WiringB2.twistRoot data j₀ m r)).1 := by
  classical
  set G : CycSubH (nearCurve j₀) p :=
    rootsEquivCycSubH (nearCurve j₀) hp2 data (nearCurve_j_transcendental j₀) r with hGdef
  set G'' : CycSubH (nearCurve j₀) p :=
    rootsEquivCycSubH (nearCurve j₀) hp2 data (nearCurve_j_transcendental j₀)
      (WiringB2.twistRoot data j₀ m r) with hG''def

  have hA1 : r = cycSubRoot (nearCurve j₀) hp2 data G :=
    (rootsEquivCycSubH_apply_eq_iff (nearCurve j₀) hp2 data
      (nearCurve_j_transcendental j₀) r G).mp hGdef.symm
  have hA2 : WiringB2.twistRoot data j₀ m r = cycSubRoot (nearCurve j₀) hp2 data G'' :=
    (rootsEquivCycSubH_apply_eq_iff (nearCurve j₀) hp2 data
      (nearCurve_j_transcendental j₀) (WiringB2.twistRoot data j₀ m r) G'').mp hG''def.symm

  have hordg : addOrderOf (cycSubGen (nearCurve j₀) G) = p := addOrderOf_cycSubGen _ G
  have hordτg : addOrderOf (B3.nearTransport j₀ m (cycSubGen (nearCurve j₀) G)) = p := by
    rw [HequivDev.addOrderOf_nearTransport]; exact hordg

  have hQel : ((nearCurve j₀).veluQuotient
      ((nearCurve j₀).oddOrderSummingSet (cycSubGen (nearCurve j₀) G) ((p - 1) / 2))).IsElliptic :=
    isElliptic_veluQuotient_cycSubSummingSet (nearCurve j₀) hp2 G
  have hΔ' : ((nearCurve j₀).veluQuotient ((nearCurve j₀).oddOrderSummingSet
      (B3.nearTransport j₀ m (cycSubGen (nearCurve j₀) G)) ((p - 1) / 2))).Δ ≠ 0 :=
    WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero two_ne_zero
      (nearCurve j₀) ((p - 1) / 2) _ (by rw [hordτg, two_mul_pred_div_two_add_one hp2])
  have hQel' : ((nearCurve j₀).veluQuotient ((nearCurve j₀).oddOrderSummingSet
      (B3.nearTransport j₀ m (cycSubGen (nearCurve j₀) G)) ((p - 1) / 2))).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ'⟩

  have hB := HequivDev.j_quot_transport j₀ m (cycSubGen (nearCurve j₀) G) ((p - 1) / 2)
    hQel hQel'

  have hjj : (cycSubRoot (nearCurve j₀) hp2 data G'').1 =
      @WeierstrassCurve.j H _ _ hQel' := by
    calc (cycSubRoot (nearCurve j₀) hp2 data G'').1
        = (WiringB2.twistRoot data j₀ m r).1 := by rw [← hA2]
      _ = (m : H ≃ₐ[Qbar] H) r.1 := rfl
      _ = (m : H ≃ₐ[Qbar] H) (cycSubRoot (nearCurve j₀) hp2 data G).1 := by rw [← hA1]
      _ = (m : H ≃ₐ[Qbar] H) (@WeierstrassCurve.j H _ _ hQel) := rfl
      _ = @WeierstrassCurve.j H _ _ hQel' := hB.symm

  have hzm : AddSubgroup.zmultiples (cycSubGen (nearCurve j₀) G'') =
      AddSubgroup.zmultiples (B3.nearTransport j₀ m (cycSubGen (nearCurve j₀) G)) :=
    WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental (nearCurve j₀)
      (transcendental_rat_of_transcendental_qbar (nearCurve_j_transcendental j₀)) ((p - 1) / 2)
      (cycSubGen (nearCurve j₀) G'') (B3.nearTransport j₀ m (cycSubGen (nearCurve j₀) G))
      (by rw [addOrderOf_cycSubGen, two_mul_pred_div_two_add_one hp2])
      (by rw [hordτg, two_mul_pred_div_two_add_one hp2])
      (isElliptic_veluQuotient_cycSubSummingSet (nearCurve j₀) hp2 G'').isUnit.ne_zero
      hΔ' hjj

  calc (AddEquiv.mapAddSubgroup (B3.nearTransport j₀ m)).toEquiv G.1
      = B3.b3Act j₀ m G.1 := rfl
    _ = B3.b3Act j₀ m (AddSubgroup.zmultiples (cycSubGen (nearCurve j₀) G)) := by
        rw [← coe_eq_zmultiples_cycSubGen]
    _ = AddSubgroup.zmultiples (B3.nearTransport j₀ m (cycSubGen (nearCurve j₀) G)) :=
        B3.b3Act_zmultiples j₀ m (cycSubGen (nearCurve j₀) G)
    _ = AddSubgroup.zmultiples (cycSubGen (nearCurve j₀) G'') := hzm.symm
    _ = G''.1 := (coe_eq_zmultiples_cycSubGen (nearCurve j₀) G'').symm

open ModularCurve.B3 WeierstrassCurve.Affine

namespace ModularCurve
p2m_export "ModularCurve" "ModularPolynomialData Emb Induces SamePlace CycSub SameOrbit EMD jBar jpBar modularFunctionFieldBar B3.nearCurve_map_of_mem_monodromy B3.nearTransport B3.nearTransport_some B3.b3Act B3.b3Act_zmultiples TatePoint.isAlgClosed_H TatePoint.charZero_H exists_place_of_emb samePlace_iff_exists_monodromy natCard_normalized_algHom_jBar_eq_toNat_ord place_eq_of_induces exists_modularPolynomialData_evalSymm exists_emb_equiv_rootsAt B3.b3_specialisationEquivariance"
namespace HdictScratch
p2m_open "ModularCurve"

section Generic

variable {A : Type*} [AddGroup A] {g : A} {n : ℕ}

private lemma nsmul_ne_zero_of_le {k : ℕ} (hord : addOrderOf g = 2 * n + 1)
    (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) : k • g ≠ 0 := fun h => by
  have : 2 * n + 1 ≤ k := hord ▸ Nat.le_of_dvd hk1 (addOrderOf_dvd_of_nsmul_eq_zero h)
  omega

private lemma eq_of_nsmul_eq (hord : addOrderOf g = 2 * n + 1) {k k' : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n) (hk'1 : 1 ≤ k') (hk'n : k' ≤ n)
    (h : k • g = k' • g) : k = k' := by
  wlog hle : k ≤ k' generalizing k k'
  · exact (this hk'1 hk'n hk1 hkn h.symm (le_of_not_ge hle)).symm
  have hsplit : (k' - k) • g + k • g = k' • g := by
    rw [← add_nsmul, Nat.sub_add_cancel hle]
  rw [← h] at hsplit
  have h0 : (k' - k) • g = 0 := by
    have hs : (k' - k) • g + k • g = 0 + k • g := by rw [hsplit, zero_add]
    exact add_right_cancel hs
  rcases Nat.eq_zero_or_pos (k' - k) with he | hp
  · omega
  · exact absurd h0 (nsmul_ne_zero_of_le hord hp (by omega))

private lemma nsmul_ne_neg_nsmul (hord : addOrderOf g = 2 * n + 1) {k k' : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n) (hk'1 : 1 ≤ k') (hk'n : k' ≤ n) :
    k • g ≠ -(k' • g) := fun h => by
  have h0 : (k + k') • g = 0 := by rw [add_nsmul, h, neg_add_cancel]
  exact nsmul_ne_zero_of_le hord (by omega) (by omega) h0

end Generic

section Fields

variable {F : Type*} [Field F]

private lemma veluGy_eq_zero_iff (W : WeierstrassCurve F) (x y : F) :
    W.veluGy x y = 0 ↔ y = W.toAffine.negY x y := by
  have : W.toAffine.negY x y = -y - W.a₁ * x - W.a₃ := rfl
  rw [this, WeierstrassCurve.veluGy, neg_eq_zero]
  constructor <;> intro h <;> linear_combination h

end Fields

section Main

variable (E : WeierstrassCurve H) {p : ℕ} [Fact p.Prime]

private lemma exists_some_of_mem_cycSubSummingSet (hp2 : p ≠ 2) (G : CycSubH E p)
    {P : H × H} (hP : P ∈ cycSubSummingSet E G) :
    ∃ (k : ℕ) (_ : 1 ≤ k) (_ : k ≤ (p - 1) / 2) (h : E.toAffine.Nonsingular P.1 P.2),
      (k • cycSubGen E G : E.toAffine.Point) = Point.some P.1 P.2 h := by
  rw [cycSubSummingSet_def, mem_oddOrderSummingSet] at hP
  obtain ⟨k, hk1, hkn, hcoords⟩ := hP
  have hord : addOrderOf (cycSubGen E G) = 2 * ((p - 1) / 2) + 1 := by
    rw [addOrderOf_cycSubGen, two_mul_pred_div_two_add_one hp2]
  have hne : k • cycSubGen E G ≠ 0 :=
    nsmul_ne_zero_of_le hord hk1 (by omega)
  rcases hQ : (k • cycSubGen E G) with _ | ⟨x, y, hxy⟩
  · exact absurd hQ hne
  · rw [hQ, Point.coordsOrZero_some] at hcoords
    refine ⟨k, hk1, hkn, ?_, ?_⟩
    · exact hcoords ▸ hxy
    · rw [hQ]; congr 1 <;> simp [← hcoords]

theorem isOddVeluSet_cycSubSummingSet (hp2 : p ≠ 2) (G : CycSubH E p) :
    E.IsOddVeluSet (cycSubSummingSet E G) := by
  have hord : addOrderOf (cycSubGen E G) = 2 * ((p - 1) / 2) + 1 := by
    rw [addOrderOf_cycSubGen, two_mul_pred_div_two_add_one hp2]
  refine ⟨fun P hP => ?_, fun P hP => ?_, fun P hP P' hP' hx => ?_⟩
  ·
    obtain ⟨k, _, _, h, _⟩ := exists_some_of_mem_cycSubSummingSet E hp2 G hP
    exact h.1
  ·
    obtain ⟨k, hk1, hkn, h, hsome⟩ := exists_some_of_mem_cycSubSummingSet E hp2 G hP
    intro hgy
    have hy : P.2 = E.toAffine.negY P.1 P.2 := (veluGy_eq_zero_iff E P.1 P.2).mp hgy
    have h2 : (2 * k) • cycSubGen E G = 0 := by
      rw [two_mul, add_nsmul, hsome, add_eq_zero_iff_eq_neg, Point.neg_some]
      simp only [Point.some.injEq, true_and]
      exact hy
    exact nsmul_ne_zero_of_le hord (by omega) (by omega) h2
  ·
    obtain ⟨k, hk1, hkn, h, hsome⟩ := exists_some_of_mem_cycSubSummingSet E hp2 G hP
    obtain ⟨k', hk'1, hk'n, h', hsome'⟩ := exists_some_of_mem_cycSubSummingSet E hp2 G hP'
    rcases (Point.X_eq_iff (h₁ := h) (h₂ := h')).mp hx with heq | hneg
    · have hkeq : k = k' := eq_of_nsmul_eq hord hk1 hkn hk'1 hk'n (by rw [hsome, hsome', heq])
      have := hsome.symm.trans (hkeq ▸ hsome')
      exact Prod.ext ((Point.some.injEq ..).mp this).1 ((Point.some.injEq ..).mp this).2
    · exact absurd (hsome.trans (hneg.trans (congrArg Neg.neg hsome'.symm)))
        (nsmul_ne_neg_nsmul hord hk1 hkn hk'1 hk'n)

theorem mem_cycSubSummingSet_lift (hp2 : p ≠ 2) (G : CycSubH E p)
    {P : H × H} (hP : P ∈ cycSubSummingSet E G) :
    ∃ h : E.toAffine.Nonsingular P.1 P.2, Point.some P.1 P.2 h ∈ G.1 := by
  obtain ⟨k, _, _, h, hsome⟩ := exists_some_of_mem_cycSubSummingSet E hp2 G hP
  refine ⟨h, ?_⟩
  rw [coe_eq_zmultiples_cycSubGen E G, ← hsome]
  exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) k

end Main

theorem hdict_rootsEquivCycSubH (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (j₀ : Qbar)
    (data : ModularPolynomialData p) :
    ∀ r : RootsAt data (nearCurve j₀).j, ∃ S : Finset (H × H),
      (nearCurve j₀).IsOddVeluSet S ∧
      (∀ P ∈ S, ∃ h : (nearCurve j₀).toAffine.Nonsingular P.1 P.2,
        WeierstrassCurve.Affine.Point.some P.1 P.2 h ∈
          (rootsEquivCycSubH (nearCurve j₀) hp2 data (nearCurve_j_transcendental j₀) r).1) ∧
      ∃ hQ : ((nearCurve j₀).veluQuotient S).IsElliptic,
        @WeierstrassCurve.j H _ ((nearCurve j₀).veluQuotient S) hQ = r.1 := by
  intro r
  set G := rootsEquivCycSubH (nearCurve j₀) hp2 data (nearCurve_j_transcendental j₀) r with hGdef
  refine ⟨cycSubSummingSet (nearCurve j₀) G,
    isOddVeluSet_cycSubSummingSet (nearCurve j₀) hp2 G,
    fun P hP => mem_cycSubSummingSet_lift (nearCurve j₀) hp2 G hP,
    isElliptic_veluQuotient_cycSubSummingSet (nearCurve j₀) hp2 G, ?_⟩
  have hreq : r = cycSubRoot (nearCurve j₀) hp2 data G :=
    (rootsEquivCycSubH_apply_eq_iff (nearCurve j₀) hp2 data
      (nearCurve_j_transcendental j₀) r G).mp hGdef.symm
  rw [hreq, cycSubRoot_coe]

end ModularCurve.HdictScratch

p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.exists_elliptic_cycSub_orbitMap_prime_of_ne_two (p : ℕ) [Fact p.Prime]
    (j₀ : AlgebraicClosure ℚ) (hp2 : p ≠ 2) :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      ∃ f : CycSub E₀ p →
          {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) //
            0 < w.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₀)},
        (∀ H H' : CycSub E₀ p, f H = f H' ↔ SameOrbit E₀ H.1 H'.1) ∧
        ∀ w : {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) //
            0 < w.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₀)},
          ((w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).ord
              (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₀)).toNat =
            Nat.card {H : CycSub E₀ p // f H = w} := by
  obtain ⟨data, _hsymm⟩ := ModularCurve.exists_modularPolynomialData_evalSymm p
  exact ModularCurve.hbeta_of_emd_docks p j₀
    (fun ψ => ModularCurve.exists_place_of_emb p j₀ ψ)
    (ModularCurve.natCard_normalized_algHom_jBar_eq_toNat_ord p j₀)
    (fun hw hw' => ModularCurve.place_eq_of_induces hw hw')
    (ModularCurve.WiringB2.emd_of_alpha p data j₀ (embEquivRootsNear p data j₀)
      (rootsEquivCycSubH (nearCurve j₀) hp2 data (nearCurve_j_transcendental j₀))
      (ModularCurve.HdictScratch.hdict_rootsEquivCycSubH p hp2 j₀ data)
      (fun m => (AddEquiv.mapAddSubgroup (ModularCurve.B3.nearTransport j₀ m)).toEquiv)
      (fun m r => ModularCurve.hequiv_rootsEquivCycSubH p hp2 j₀ data m r)
      (ModularCurve.B3.b3_specialisationEquivariance p j₀))

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_elliptic_cycSub_orbitMap_prime_of_ne_two.ModularCurve AlgebraicCurve in

theorem solution (p : ℕ) [Fact p.Prime]
    (j₀ : AlgebraicClosure ℚ) (hp2 : p ≠ 2) :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      ∃ f : CycSub E₀ p →
          {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) //
            0 < w.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₀)},
        (∀ H H' : CycSub E₀ p, f H = f H' ↔ SameOrbit E₀ H.1 H'.1) ∧
        ∀ w : {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) //
            0 < w.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₀)},
          ((w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).ord
              (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₀)).toNat =
            Nat.card {H : CycSub E₀ p // f H = w} :=
  ModularCurve.exists_elliptic_cycSub_orbitMap_prime_of_ne_two p j₀ hp2

#print axioms solution

end S_ModularCurve_exists_elliptic_cycSub_orbitMap_prime_of_ne_two
end P2MW
export P2MW.S_ModularCurve_exists_elliptic_cycSub_orbitMap_prime_of_ne_two (solution)
