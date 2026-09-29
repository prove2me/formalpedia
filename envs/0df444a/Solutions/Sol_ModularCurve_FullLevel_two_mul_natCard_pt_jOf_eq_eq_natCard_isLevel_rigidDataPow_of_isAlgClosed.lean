-- Prove2me | solution 1 for ModularCurve.FullLevel.two_mul_natCard_pt_jOf_eq_eq_natCard_isLevel_rigidDataPow_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/db809987-2fc0-5955-816a-f6a0debe3b6b

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling

import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_two_mul_natCard_pt_jOf_eq_eq_natCard_isLevel_rigidDataPow_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

namespace K8ORB

variable {A : Type} [CommRing A] (L : LevelComponent A) {Ω : Type} [Field Ω] [Algebra A Ω]

def Fib (W₀ : WeierstrassCurve Ω) : Type := {lev : L.obj Ω // L.IsLevel W₀ lev}

abbrev Stab (W₀ : WeierstrassCurve Ω) : Subgroup (WeierstrassCurve.VariableChange Ω) :=
  MulAction.stabilizer (WeierstrassCurve.VariableChange Ω) W₀

variable (W₀ : WeierstrassCurve Ω)

scoped instance : SMul (Stab W₀) (Fib L W₀) :=
  ⟨fun C x => ⟨L.act (C : WeierstrassCurve.VariableChange Ω) x.1, by
    have h := L.isLevel_act (C : WeierstrassCurve.VariableChange Ω) W₀ x.1 x.2
    have hC : (C : WeierstrassCurve.VariableChange Ω) • W₀ = W₀ := C.2
    rwa [hC] at h⟩⟩

theorem smul_val (C : Stab W₀) (x : Fib L W₀) :
    (C • x).1 = L.act (C : WeierstrassCurve.VariableChange Ω) x.1 := rfl

scoped instance : MulAction (Stab W₀) (Fib L W₀) where
  one_smul x := Subtype.ext (L.act_one x.1)
  mul_smul C C' x := Subtype.ext (L.act_mul (C : WeierstrassCurve.VariableChange Ω) (C' : WeierstrassCurve.VariableChange Ω) x.1)

theorem natCard_fib_eq (hfree : ∀ (C : WeierstrassCurve.VariableChange Ω), C • W₀ = W₀ →
      ∀ lev : L.obj Ω, L.IsLevel W₀ lev → L.act C lev = lev → C = 1) :
    Nat.card (Fib L W₀)
      = Nat.card (MulAction.orbitRel.Quotient (Stab W₀) (Fib L W₀)) * Nat.card (Stab W₀) := by
  classical
  let G := Stab W₀
  let Q := MulAction.orbitRel.Quotient G (Fib L W₀)
  let π : Fib L W₀ → Q := fun x => (Quotient.mk (MulAction.orbitRel G (Fib L W₀)) x : Q)

  have fibEquiv : ∀ q : Q, {x : Fib L W₀ // π x = q} ≃ G := by
    intro q
    let x₀ : Fib L W₀ := q.out
    have hx₀ : π x₀ = q := q.out_eq
    refine (Equiv.ofBijective (fun g : G => (⟨g • x₀, ?_⟩ : {x : Fib L W₀ // π x = q})) ⟨?_, ?_⟩).symm
    ·
      rw [← hx₀]
      exact Quotient.sound ⟨g, rfl⟩
    · intro g g' h
      have h1 : g • x₀ = g' • x₀ := congrArg (fun z => z.1) (Subtype.ext_iff.mp h) |> fun e => Subtype.ext e
      have h2 : (g'⁻¹ * g) • x₀ = x₀ := by rw [mul_smul, h1, ← mul_smul, inv_mul_cancel, one_smul]
      have h3 : ((g'⁻¹ * g : G) : WeierstrassCurve.VariableChange Ω) = 1 :=
        hfree _ (g'⁻¹ * g).2 x₀.1 x₀.2 (congrArg Subtype.val h2)
      have : g'⁻¹ * g = 1 := Subtype.ext h3
      exact (inv_mul_eq_one.mp this).symm
    · rintro ⟨x, hx⟩
      have : (MulAction.orbitRel G (Fib L W₀)) x x₀ := Quotient.exact (hx.trans hx₀.symm)
      obtain ⟨g, hg⟩ := this
      exact ⟨g, Subtype.ext (by exact hg)⟩
  have e : Fib L W₀ ≃ Q × G :=
    (Equiv.sigmaFiberEquiv π).symm.trans ((Equiv.sigmaCongrRight fibEquiv).trans (Equiv.sigmaEquivProd Q G))
  rw [Nat.card_congr e, Nat.card_prod]

theorem nonempty_quotient_equiv (hΔ₀ : IsUnit W₀.Δ)
    (hiso : ∀ (W : WeierstrassCurve Ω) (hΔ : IsUnit W.Δ), W.jOfUnit hΔ = W₀.jOfUnit hΔ₀ →
      ∃ C : WeierstrassCurve.VariableChange Ω, C • W = W₀) :
    Nonempty (MulAction.orbitRel.Quotient (Stab W₀) (Fib L W₀) ≃
      {x : (L.toRigid).Pt Ω // (L.toRigid).jOf x = W₀.jOfUnit hΔ₀}) := by
  classical
  let R := L.toRigid
  let G := Stab W₀

  let raw : Fib L W₀ → L.Raw Ω := fun x => ⟨W₀, hΔ₀, x.1, x.2⟩
  have hrel_equiv : Equivalence (R.Rel (T := Ω)) := by
    refine ⟨RigidWeierstrassData.Rel.refl R, ?_, RigidWeierstrassData.Rel.trans R⟩
    rintro x y ⟨C, rfl⟩
    exact ⟨C⁻¹, by rw [← R.act_mul, inv_mul_cancel, R.act_one]⟩

  let f₀ : Fib L W₀ → {x : R.Pt Ω // R.jOf x = W₀.jOfUnit hΔ₀} :=
    fun x => ⟨Quot.mk _ (raw x), by rw [RigidWeierstrassData.jOf_mk]; rfl⟩
  have f₀_resp : ∀ x y : Fib L W₀, (MulAction.orbitRel G (Fib L W₀)) x y → f₀ x = f₀ y := by
    rintro x y ⟨g, rfl⟩
    apply Subtype.ext
    show Quot.mk _ (raw (g • y)) = Quot.mk _ (raw y)
    symm
    apply Quot.sound
    refine ⟨(g : WeierstrassCurve.VariableChange Ω), ?_⟩
    exact LevelComponent.Raw.ext' (g.2).symm rfl
  let f : MulAction.orbitRel.Quotient G (Fib L W₀) → {x : R.Pt Ω // R.jOf x = W₀.jOfUnit hΔ₀} :=
    Quotient.lift f₀ f₀_resp
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩⟩
  ·
    intro a b hab
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    have h1 : Quot.mk (R.Rel (T := Ω)) (raw x) = Quot.mk _ (raw y) := congrArg Subtype.val hab
    have h2 : R.Rel (raw x) (raw y) := (hrel_equiv.eqvGen_iff).mp (Quot.eqvGen_exact h1)
    obtain ⟨C, hC⟩ := h2
    have hCW : C • W₀ = W₀ := by
      have := congrArg LevelComponent.Raw.curve hC
      exact this.symm
    have hlev : y.1 = L.act C x.1 := congrArg LevelComponent.Raw.level hC
    apply Quotient.sound
    refine ⟨⟨C⁻¹, ?_⟩, ?_⟩
    · show C⁻¹ • W₀ = W₀
      conv_lhs => rw [← hCW]
      rw [← mul_smul, inv_mul_cancel, one_smul]
    · apply Subtype.ext
      show L.act C⁻¹ y.1 = x.1
      rw [hlev, ← L.act_mul, inv_mul_cancel, L.act_one]
  ·
    rintro ⟨x, hx⟩
    induction x using Quot.inductionOn with | h r => ?_
    rw [RigidWeierstrassData.jOf_mk] at hx
    obtain ⟨C, hC⟩ := hiso r.curve r.isUnit_Δ hx
    have hlevW : L.IsLevel W₀ (L.act C r.level) := by
      have := L.isLevel_act C r.curve r.level r.isLevel
      rwa [hC] at this
    refine ⟨Quotient.mk _ ⟨L.act C r.level, hlevW⟩, ?_⟩
    apply Subtype.ext
    show Quot.mk _ (raw ⟨L.act C r.level, hlevW⟩) = Quot.mk _ r
    symm
    apply Quot.sound
    exact ⟨C, LevelComponent.Raw.ext' hC.symm rfl⟩

theorem natCard_pt_mul_natCard_stabilizer_eq (hΔ₀ : IsUnit W₀.Δ)
    (hiso : ∀ (W : WeierstrassCurve Ω) (hΔ : IsUnit W.Δ), W.jOfUnit hΔ = W₀.jOfUnit hΔ₀ →
      ∃ C : WeierstrassCurve.VariableChange Ω, C • W = W₀)
    (hfree : ∀ (C : WeierstrassCurve.VariableChange Ω), C • W₀ = W₀ →
      ∀ lev : L.obj Ω, L.IsLevel W₀ lev → L.act C lev = lev → C = 1) :
    Nat.card {x : (L.toRigid).Pt Ω // (L.toRigid).jOf x = W₀.jOfUnit hΔ₀} * Nat.card (Stab W₀)
      = Nat.card {lev : L.obj Ω // L.IsLevel W₀ lev} := by
  obtain ⟨e⟩ := nonempty_quotient_equiv L W₀ hΔ₀ hiso
  rw [← Nat.card_congr e, ← natCard_fib_eq L W₀ hfree]
  rfl

end K8ORB
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_two_mul_natCard_pt_jOf_eq_eq_natCard_isLevel_rigidDataPow_of_isAlgClosed.K8ORB"

theorem solution
    (A : Type) [CommRing A]
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra A Ω] (hℓΩ : ((ℓ : ℕ) : Ω) ≠ 0)
    (W₀ : WeierstrassCurve Ω) (hΔ : IsUnit W₀.Δ) (t : Ω) (hj : W₀.jOfUnit hΔ = t) (ht0 : t ≠ 0) (ht : t ≠ 1728) :
    2 * Nat.card {x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt Ω //
        (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x = t} =
      Nat.card {lev : ((ModularCurve.gamma0PowComponent A M' hM).prod
          ((ModularCurve.levelPComponent A ℓ hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).obj Ω //
        ((ModularCurve.gamma0PowComponent A M' hM).prod
          ((ModularCurve.levelPComponent A ℓ hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).IsLevel W₀ lev} := by
  set L := (ModularCurve.gamma0PowComponent A M' hM).prod
    ((ModularCurve.levelPComponent A ℓ hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯)) with hL
  haveI hE₀ : W₀.IsElliptic := ⟨hΔ⟩
  have hj₀ : W₀.j = t := by rw [← WeierstrassCurve.jOfUnit_eq_j W₀ hΔ]; exact hj

  have hiso : ∀ (W : WeierstrassCurve Ω) (hΔ' : IsUnit W.Δ), W.jOfUnit hΔ' = W₀.jOfUnit hΔ →
      ∃ C : WeierstrassCurve.VariableChange Ω, C • W = W₀ := by
    intro W hΔ' hjW
    haveI : W.IsElliptic := ⟨hΔ'⟩
    have : W.j = W₀.j := by rwa [WeierstrassCurve.jOfUnit_eq_j, WeierstrassCurve.jOfUnit_eq_j] at hjW
    exact WeierstrassCurve.exists_variableChange_of_j_eq W W₀ this

  have hstab : Nat.card (K8ORB.Stab W₀) = 2 :=
    WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
      (F := Ω) two_ne_zero three_ne_zero W₀ (hj₀ ▸ ht0 :) (hj₀ ▸ ht :)

  have hℓΩ' : IsUnit ((ℓ : ℕ) : Ω) := isUnit_iff_ne_zero.mpr hℓΩ
  have hfree : ∀ (C : WeierstrassCurve.VariableChange Ω), C • W₀ = W₀ →
      ∀ lev : L.obj Ω, L.IsLevel W₀ lev → L.act C lev = lev → C = 1 := by
    intro C hC lev hlev hact
    have hD : (lev.2.1).variableChange C = lev.2.1 := congrArg (fun z => z.2.1) hact
    exact ModularCurve.IsLevelPStructure.variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
      ℓ hℓ3 hℓΩ' W₀ hΔ lev.2.1 hlev.2.1 C hC hD
  have key := K8ORB.natCard_pt_mul_natCard_stabilizer_eq L W₀ hΔ hiso hfree
  rw [hstab] at key
  subst hj
  show 2 * Nat.card {x : (L.toRigid).Pt Ω // (L.toRigid).jOf x = W₀.jOfUnit hΔ} = _
  omega

end S_ModularCurve_FullLevel_two_mul_natCard_pt_jOf_eq_eq_natCard_isLevel_rigidDataPow_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_FullLevel_two_mul_natCard_pt_jOf_eq_eq_natCard_isLevel_rigidDataPow_of_isAlgClosed (solution)
