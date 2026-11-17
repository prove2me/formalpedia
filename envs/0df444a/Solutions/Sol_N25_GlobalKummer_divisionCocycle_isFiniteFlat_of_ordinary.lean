-- Prove2me | solution 1 for N25.GlobalKummer.divisionCocycle_isFiniteFlat_of_ordinary
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:09:10.185985+00:00
-- url     : https://prove2.me/submissions/694ddc45-e4e6-423a-a6e9-dc603978d075

import Definitions.Def_N25_LocalFiniteFlatClasses
import Definitions.Def_N25_OrdinaryKummerFiniteFlat
import Definitions.Def_N25_LocalKummerOperators
import Theorems.Thm_groupCohomology_IsFiniteFlatCocycle_of_map_injective
import Definitions.Def_GroupCohomology_CocycleExtensionAction
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open CategoryTheory groupCohomology

namespace N25.GlobalKummer

local instance ordinaryDivisionPrime_sbfc5bf : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- Ordinary division-extension flatness implies the selected operator's local
Kummer condition, by the literal inclusion of its kernel into ordinary 71-torsion.
The ordinary finite-flat construction remains the explicit premise. -/
theorem _root_.solution
    (hPhi : PhiFiveZero) (hN71 : OrdinaryKummerFiniteFlat)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J)) :
    IsFiniteFlatCocycle 71 (localKernelRep hPhi).ρ
      (fun σ => divisionCocycle hPhi P Q hQ (localGaloisToGlobal 71 σ)) := by
  letI := vModule hPhi
  let r := localGaloisToGlobal 71
  let T := AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
    (ModularCurve.xHFunctionFieldBar 25 H25) 71
  let ρT := (ModularCurve.JH.torsionGaloisRep 25 H25 71).comp r
  have hmul : (71 : ℕ) • Q = rhoEnd (P : J) := by
    have h := congrArg (fun f : J →+ J => f Q) (rhoEnd_comp_piEnd hPhi)
    change rhoEnd (piEnd Q) = (71 : ℕ) • Q at h
    rw [hQ] at h
    exact h.symm
  have h71 : (71 : ℕ) • Q ∈ M := by
    intro σ
    rw [hmul, rhoEnd_galois_comm, P.property σ]
  let cg := divisionCocycle hPhi P Q hQ
  let c : cocycles₁ (localKernelRep hPhi) :=
    ⟨fun σ => cg (r σ), by
      apply (mem_cocycles₁_iff _).mpr
      intro σ τ
      change cg (r (σ * τ)) = (vRep hPhi).ρ (r σ) (cg (r τ)) + cg (r σ)
      rw [map_mul]
      exact (mem_cocycles₁_iff _).mp cg.property (r σ) (r τ)⟩
  let d : cocycles₁ (Rep.of ρT) :=
    ⟨fun σ => ⟨r σ • Q - Q, by
      apply AlgebraicCurve.Pic0.mem_torsion.mpr
      have hNat : (71 : ℕ) • (r σ • Q - Q) = 0 := by
        have hs : r σ • ((71 : ℕ) • Q) = (71 : ℕ) • (r σ • Q) :=
          (DistribSMul.toAddMonoidHom J (r σ)).map_nsmul 71 Q
        rw [nsmul_sub, ← hs, h71 (r σ), sub_self]
      exact (Nat.cast_smul_eq_nsmul ℤ 71 (r σ • Q - Q)).trans hNat⟩, by
      apply (mem_cocycles₁_iff _).mpr
      intro σ τ
      apply Subtype.ext
      change r (σ * τ) • Q - Q = r σ • (r τ • Q - Q) + (r σ • Q - Q)
      rw [map_mul, mul_smul, smul_sub]
      abel⟩
  have hscalar (a : ZMod 71) (v : T) : a.val • v = a • v := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 71)]
    simp
  have hd : IsFiniteFlatCocycle 71 ρT d := by
    have h := hN71 Q h71
    change IsFiniteFlatRepresentation 71 (fun σ (x : T × ZMod 71) =>
      (ρT σ x.1 + x.2.val • d σ, x.2)) at h
    simpa only [IsFiniteFlatCocycle, hscalar] using h
  have hkill (v : ↥V) : (71 : ℕ) • (v : J) = 0 := by
    have h := congrArg (fun f : J →+ J => f (v : J)) (rhoEnd_comp_piEnd hPhi)
    change rhoEnd (piEnd (v : J)) = (71 : ℕ) • (v : J) at h
    rw [show piEnd (v : J) = 0 from v.2, map_zero] at h
    exact h.symm
  let j : ↥V →+ T :=
    { toFun := fun v => ⟨(v : J), by
        apply AlgebraicCurve.Pic0.mem_torsion.mpr
        exact (Nat.cast_smul_eq_nsmul ℤ 71 (v : J)).trans (hkill v)⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let i : (localKernelRep hPhi) →ₗ[ZMod 71] T :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a v => ZMod.map_smul j a v }
  have hi : Function.Injective i := by
    intro v w h
    exact Subtype.ext (congrArg (fun z : T => (z : J)) h)
  apply IsFiniteFlatCocycle.of_map_injective 71 (localKernelRep hPhi).ρ ρT c d i hi
  · intro σ v
    apply Subtype.ext
    rfl
  · intro σ
    apply Subtype.ext
    rfl
  · exact hd

end N25.GlobalKummer
