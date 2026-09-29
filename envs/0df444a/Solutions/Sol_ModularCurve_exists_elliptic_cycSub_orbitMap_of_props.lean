-- Prove2me | solution 1 for ModularCurve.exists_elliptic_cycSub_orbitMap_of_props
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/8378e0da-1b37-505b-bc01-69fdc4656766

import Definitions.Def_ModularCurve_EMD
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_CycSubRootBridgeN
import Definitions.Def_ModularCurve_SpecialisationBridge
import Definitions.Def_ModularCurve_TatePoint
import Definitions.Def_HahnSeries_Monodromy
import Theorems.Thm_ModularCurve_exists_place_of_emb
import Theorems.Thm_ModularCurve_samePlace_iff_exists_monodromy
import Theorems.Thm_ModularCurve_natCard_normalized_algHom_jBar_eq_toNat_ord
import Theorems.Thm_ModularCurve_place_eq_of_induces
import Theorems.Thm_ModularCurve_exists_emb_equiv_rootsAt
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_B3_specialisationEquivariance_level
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_elliptic_cycSub_orbitMap_of_props
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

noncomputable section

open scoped Classical

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_elliptic_cycSub_orbitMap_of_props.ModularCurve ModularCurve.TatePoint AlgebraicCurve WeierstrassCurve Polynomial"

attribute [local instance] ModularCurve.TatePoint.isAlgClosed_H ModularCurve.TatePoint.charZero_H

namespace ModularCurve
p2m_export "ModularCurve" "Emb Induces SamePlace CycSub SameOrbit EMD jBar jpBar modularFunctionFieldBar ModularPolynomialData TatePoint.dictN TatePoint.isAlgClosed_H TatePoint.charZero_H B3.nearTransport B3.b3Act exists_place_of_emb samePlace_iff_exists_monodromy natCard_normalized_algHom_jBar_eq_toNat_ord place_eq_of_induces exists_emb_equiv_rootsAt nonempty_modularPolynomialData B3.specialisationEquivariance_level"
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

theorem emd_of_alphaN (p : ℕ) [NeZero p] (data : ModularPolynomialData p)
    (j₀ : Qbar)
    (hB1 : {e : Emb p j₀ ≃ RootsAt data (nearCurve j₀).j //
      ∀ ψ : Emb p j₀, (e ψ).1 = ψ.1 (jpBar p)})
    (dict : RootsAt data (nearCurve j₀).j ≃ CycSubH (nearCurve j₀) p)
    (act : HahnSeries.monodromy Qbar → (AddSubgroup (nearCurve j₀).toAffine.Point ≃
      AddSubgroup (nearCurve j₀).toAffine.Point))
    (hequiv : ∀ (m : HahnSeries.monodromy Qbar) (r : RootsAt data (nearCurve j₀).j),
      act m (dict r).1 = (dict (twistRoot data j₀ m r)).1)
    (hB3 : ∃ β : CycSubH (nearCurve j₀) p ≃ CycSub (WeierstrassCurve.ofJ j₀) p,
      ∀ G G' : CycSubH (nearCurve j₀) p,
        (∃ m : HahnSeries.monodromy Qbar, act m G.1 = G'.1) ↔
          SameOrbit (WeierstrassCurve.ofJ j₀) (β G).1 (β G').1) :
    EMD p j₀ := by
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

namespace ModularCurve p2m_export "ModularCurve" "Emb Induces SamePlace CycSub SameOrbit EMD jBar jpBar modularFunctionFieldBar ModularPolynomialData TatePoint.dictN TatePoint.isAlgClosed_H TatePoint.charZero_H B3.nearTransport B3.b3Act exists_place_of_emb samePlace_iff_exists_monodromy natCard_normalized_algHom_jBar_eq_toNat_ord place_eq_of_induces exists_emb_equiv_rootsAt nonempty_modularPolynomialData B3.specialisationEquivariance_level" end ModularCurve
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

theorem solution (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ)
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (hequivN : ∀ data : ModularPolynomialData N,
      ∀ (m : HahnSeries.monodromy Qbar) (r r' : RootsAt data (nearCurve j₀).j),
        r'.1 = (m : H ≃ₐ[Qbar] H) r.1 →
        B3.b3Act j₀ m (dictN N data j₀ hW1 hW2 hW3 r).1 = (dictN N data j₀ hW1 hW2 hW3 r').1)
    :
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
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  exact ModularCurve.hbeta_of_emd_docks N j₀
    (fun ψ => ModularCurve.exists_place_of_emb N j₀ ψ)
    (ModularCurve.natCard_normalized_algHom_jBar_eq_toNat_ord N j₀)
    (fun hw hw' => ModularCurve.place_eq_of_induces hw hw')
    (ModularCurve.WiringB2.emd_of_alphaN N data j₀ (embEquivRootsNear N data j₀)
      (dictN N data j₀ hW1 hW2 hW3)
      (fun m => (AddEquiv.mapAddSubgroup (ModularCurve.B3.nearTransport j₀ m)).toEquiv)
      (fun m r => hequivN data m r (ModularCurve.WiringB2.twistRoot data j₀ m r) rfl)
      (ModularCurve.B3.specialisationEquivariance_level N j₀))

end

end S_ModularCurve_exists_elliptic_cycSub_orbitMap_of_props
end P2MW
export P2MW.S_ModularCurve_exists_elliptic_cycSub_orbitMap_of_props (solution)
