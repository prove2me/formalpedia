-- Prove2me | solution 1 for N25.exists_cyclotomic_quotient_of_cusp
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:09.501768+00:00
-- url     : https://prove2.me/submissions/fd3f3ea8-b3d6-49e1-943e-cbac0e956731

import Definitions.Def_N25_GlobalKummer
import Theorems.Thm_N25_piEnd_projection_eq_zero
import Definitions.Def_N25_LocalKummerPolynomial
import Theorems.Thm_N25_GlobalKummer_cyclotomic_roots_equiv
import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_semilinearSmul
import Theorems.Thm_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_isCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

namespace N25

local instance primeSeventyOnePairing_se09c0d : Fact (Nat.Prime 71) := ⟨by decide⟩

private theorem pairing_projection_preserves
    {T K : Type*} [AddCommGroup T] [Field K]
    (f : AddChar T K) (g : T →+ T)
    (h71 : ∀ x, f x ^ 71 = 1) (h5 : ∀ x, f (g x) ^ 5 = f x) (x : T) :
    f (3 • x + 18 • g x + 22 • g (g x) + 42 • g (g (g x))) = f x := by
  have hp (y : T) : f (g y) = f y ^ 57 := by
    have hpower : f (g y) ^ (5 * 57) = f (g y) := by
      rw [show (5 * 57 : ℕ) = 71 * 4 + 1 by norm_num,
        pow_add, pow_mul, h71, one_pow, pow_one, one_mul]
    rw [← hpower, pow_mul, h5]
  simp only [f.map_add_eq_mul, f.map_nsmul_eq_pow, hp, ← pow_mul, ← pow_add]
  rw [show (3 + 57 * 18 + (57 * 57) * 22 + ((57 * 57) * 57) * 42 : ℕ) =
    71 * 110572 + 1 by norm_num,
    pow_add, pow_mul, h71, one_pow, pow_one, one_mul]

private theorem exists_nontrivial_kernel_pairing
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25)]
    (hPhi : PhiFiveZero)
    (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) 71)
 (he : Function.Injective e.toHom)
    (c : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) 71)
    (hcne : c ≠ 0) (hgamma : gamma (c : J) = 5 • (c : J)) :
    ∃ x : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) 71,
      piEnd (x : J) = 0 ∧ e.pair x c ≠ 1 := by
  classical
  let T := AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
    (ModularCurve.xHFunctionFieldBar 25 H25) 71
  let g := AlgebraicCurve.SemilinearAut.ofAlgAut
    (ModularCurve.diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide)))
  have hgc : g • c = 5 • c := by
    apply Subtype.ext
    exact hgamma
  let f : AddChar T (AlgebraicClosure ℚ) :=
    { toFun := fun x => e.pair x c
      map_zero_eq_one' := e.pair_zero_left c
      map_add_eq_mul' := fun x y => e.pair_add_left x y c }
  let gt : T →+ T := DistribSMul.toAddMonoidHom T g
  have h5 (x : T) : f (gt x) ^ 5 = f x := by
    have h := e.pair_smul
      (ModularCurve.diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide))) x c
    change e.pair (g • x) (g • c) = e.pair x c at h
    rw [hgc] at h
    have hmul := (e.toChar (g • x)).map_nsmul_eq_pow 5 c
    change e.pair (g • x) (5 • c) = e.pair (g • x) c ^ 5 at hmul
    rw [hmul] at h
    exact h
  have hproj (x : T) :
      e.pair (3 • x + 18 • (g • x) + 22 • (g • (g • x)) +
        42 • (g • (g • (g • x)))) c = e.pair x c :=
    pairing_projection_preserves f gt (fun y => AlgebraicCurve.HomPic0Gm.apply_pow_eq_one (e.toChar y) c) h5 x
  by_contra hn
  push Not at hn
  apply hcne
  apply he
  rw [map_zero]
  change e.toChar c = 1
  apply DFunLike.ext
  intro x
  have h71 : 71 • (x : J) = 0 := by
    simpa only [natCast_zsmul] using AlgebraicCurve.Pic0.mem_torsion.mp x.2
  have hcoe (y : T) : ((g • y : T) : J) = gamma (y : J) := rfl
  have hy : piEnd ((3 • x + 18 • (g • x) + 22 • (g • (g • x)) +
      42 • (g • (g • (g • x))) : T) : J) = 0 := by
    simpa only [AddSubgroup.coe_add, AddSubgroup.coe_nsmul, hcoe] using
      piEnd_projection_eq_zero hPhi (x : J) h71
  have hx := hn (3 • x + 18 • (g • x) + 22 • (g • (g • x)) +
      42 • (g • (g • (g • x)))) hy
  rw [hproj] at hx
  change e.pair c x = 1
  rw [e.pair_swap_eq_inv, hx, inv_one]

private theorem pairing_fixed_cusp_galois
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25)]
    (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) 71)
    (c : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) 71)
    (hcfix : ∀ σ : Gal, σ • (c : J) = (c : J)) (σ : Gal)
    (x : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) 71) :
    e.pair (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField 25 H25) σ • x) c =
      σ (e.pair x c) := by
  have h := e.pair_semilinearSmul
    (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField 25 H25) σ) x c
  have hc : ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField 25 H25) σ • c = c := by
    apply Subtype.ext
    change σ • (c : J) = (c : J)
    exact hcfix σ
  rw [hc] at h
  exact h

/-- Evaluation of the divisorial Weil pairing against a fixed torsion cusp,
expressed in actual roots-of-unity coordinates, gives the cyclotomic quotient.
A nontrivial evaluation on the selected kernel makes this quotient surjective. -/
theorem exists_quotient_of_cusp_pairing
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25)]
    (hPhi : PhiFiveZero)
    (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) 71)

    (c : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) 71)
    (hcfix : ∀ σ : Gal, σ • (c : J) = (c : J))
    (he : Function.Injective e.toHom) (hcne : c ≠ 0)
    (hgamma : gamma (c : J) = 5 • (c : J)) :
    ∃ (coord : ZMod 71 ≃+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)))
      (q : ↥V →+ ZMod 71),
      Function.Surjective q ∧
      (∀ (σ : Gal) (v : ↥V), q (vAct σ v) =
        (ExtCitation.cycloChar 71 σ : ZMod 71) * q v) ∧
      ∀ (v : ↥V) (hv : (71 : ℤ) • (v : J) = 0),
        (Additive.toMul (coord (q v))).val.val =
          e.pair ⟨(v : J), AlgebraicCurve.Pic0.mem_torsion.mpr hv⟩ c := by
  classical
  have hnonzero := exists_nontrivial_kernel_pairing hPhi e he c hcne hgamma
  let := GlobalKummer.vModule hPhi
  let T := AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
    (ModularCurve.xHFunctionFieldBar 25 H25) 71
  have hv71 (v : ↥V) : (71 : ℤ) • (v : J) = 0 := by
    have h := congrArg (fun f : J →+ J => f (v : J)) (rhoEnd_comp_piEnd hPhi)
    change rhoEnd (piEnd (v : J)) = 71 • (v : J) at h
    rw [show piEnd (v : J) = 0 from v.2, map_zero] at h
    exact (natCast_zsmul (v : J) (71 : ℕ)).trans h.symm
  let toT : ↥V →+ T :=
    { toFun := fun v => ⟨(v : J), AlgebraicCurve.Pic0.mem_torsion.mpr (hv71 v)⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let r : ↥V →+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)) :=
    { toFun := fun v => Additive.ofMul
        ⟨Units.mk0 (e.pair (toT v) c) (e.pair_ne_zero _ _), by
          change (Units.mk0 (e.pair (toT v) c) (e.pair_ne_zero _ _)) ^ 71 = 1
          apply Units.ext
          exact AlgebraicCurve.HomPic0Gm.apply_pow_eq_one (e.toChar (toT v)) c⟩
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Units.ext
        exact e.pair_zero_left c
      map_add' := by
        intro v w
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Units.ext
        exact e.pair_add_left (toT v) (toT w) c }
  obtain ⟨coord, hcoord⟩ := GlobalKummer.cyclotomic_roots_equiv
  let q : ↥V →+ ZMod 71 := coord.symm.toAddMonoidHom.comp r
  have hqr (v : ↥V) : coord (q v) = r v := coord.apply_symm_apply (r v)
  have hqne : ∃ v, q v ≠ 0 := by
    obtain ⟨x, hx, he⟩ := hnonzero
    refine ⟨⟨(x : J), hx⟩, fun hz => he ?_⟩
    have h := congrArg (fun z =>
      (Additive.toMul (coord z)).val.val) hz
    rw [hqr, map_zero] at h
    change e.pair (toT (⟨(x : J), hx⟩ : ↥V)) c = 1 at h
    have ht : toT (⟨(x : J), hx⟩ : ↥V) = x := Subtype.ext rfl
    rw [ht] at h
    exact h
  have hsurj : Function.Surjective q := by
    obtain ⟨v, hv⟩ := hqne
    intro t
    refine ⟨(t / q v).val • v, ?_⟩
    simp only [map_nsmul, nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]
    exact div_mul_cancel₀ _ hv
  have hgal (σ : Gal) (v : ↥V) : q (vAct σ v) =
      (ExtCitation.cycloChar 71 σ : ZMod 71) * q v := by
    apply coord.injective
    rw [hqr, hcoord, hqr]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    have ht : toT (vAct σ v) =
        ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField 25 H25) σ • toT v :=
      Subtype.ext rfl
    change e.pair (toT (vAct σ v)) c = σ (e.pair (toT v) c)
    rw [ht]
    exact pairing_fixed_cusp_galois e c hcfix σ (toT v)
  refine ⟨coord, q, hsurj, hgal, ?_⟩
  intro v hv
  rw [hqr]
  rfl

/-- A nonzero rational cusp of order seventy-one in the eigenvalue-five line
induces a surjective cyclotomic quotient of the literal selected kernel. -/
theorem _root_.solution (hPhi : PhiFiveZero)
    (c : J) (hcne : c ≠ 0) (hc71 : 71 • c = 0)
    (hgamma : gamma c = 5 • c) (hcfix : ∀ σ : Gal, σ • c = c) :
    ∃ q : ↥V →+ ZMod 71, Function.Surjective q ∧
      ∀ (σ : Gal) (v : ↥V), q (vAct σ v) =
        (ExtCitation.cycloChar 71 σ : ZMod 71) * q v := by
  let hcurve : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
      (AlgebraicClosure ℚ) 25 H25).1
  let hprincipal : AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) :=
    AlgebraicCurve.IsCurveOver.hasPrincipalDivisors
  let hindex : (CohCarrier.GammaH 25 H25).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH 25 H25)
  have hfg := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH 25 H25)
    (ModularCurve.translation_mem_GammaH 25 H25)
  obtain ⟨e⟩ := @AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed
    (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar 25 H25)
    inferInstance inferInstance inferInstance inferInstance hfg hcurve 71 inferInstance
  have hinj := @AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_isCurveOver
    (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar 25 H25)
    inferInstance inferInstance inferInstance inferInstance inferInstance hfg hcurve 71 inferInstance e
  let ct : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) 71 :=
    ⟨c, AlgebraicCurve.Pic0.mem_torsion.mpr ((natCast_zsmul c (71 : ℕ)).trans hc71)⟩
  have hct : ct ≠ 0 := fun h => hcne (congrArg Subtype.val h)
  obtain ⟨_, q, hq, hqgal, _⟩ :=
    @exists_quotient_of_cusp_pairing hprincipal hPhi e ct hcfix hinj hct hgamma
  exact ⟨q, hq, hqgal⟩

end N25
