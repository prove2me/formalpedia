-- Prove2me | solution 1 for ModularCurve.FullLevel.tateHecke_mul_tateGal_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/b30a2675-b591-5672-bf51-9a3f0df8c847

import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_galois_smul_genOpH_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.galJac FullLevel.heckeJac FullLevel.tateEnd FullLevel.tateGal FullLevel.tateHecke diamondHBar heckeOperatorHAlong HeckeAlg heckeGen galois_smul_genOpH_comm"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH jacComp Idx Idx.ext Idx.val_smul Idx.val_pow Jac Jac.ext galJac galJac_eval heckeGenJac heckeGenJac_eval HeckeGenCommute heckeJac heckeJac_heckeGen heckeJac_heckeGen_of_not tateEnd tateGal tateHecke"
p2m_open "ModularCurve.FullLevel ModularCurve"

namespace TateHeckeGalComm

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem smul_pow (σ : Gal) (d : (ZMod q)ˣ) (ζ : Idx q) : σ • (ζ.pow d) = (σ • ζ).pow d :=
  Idx.ext (by rw [Idx.val_smul, Idx.val_pow, Idx.val_pow, Idx.val_smul, map_pow])

variable [NeZero M']

scoped instance neZero_sq_mul : NeZero (q ^ 2 * M') :=
  ⟨mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩

theorem smul_heckeOperatorHAlong (σ : Gal) {ℓ : ℕ} (hℓ : ℓ.Prime) (P : jacComp q M') :
    σ • (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
        heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ P) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
        heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ (σ • P)) := by
  by_cases h : ℓ ∣ q ^ 2 * M'
  · exact galois_smul_genOpH_comm (q ^ 2 * M') (levelH q M') (∅ : Set ℕ) σ (.U ℓ hℓ h) P
  · exact galois_smul_genOpH_comm (q ^ 2 * M') (levelH q M') (∅ : Set ℕ) σ
      (.T ℓ hℓ (Set.notMem_empty ℓ) h) P

theorem smul_diamondHBar (σ : Gal) (d : (ZMod (q ^ 2 * M'))ˣ) (P : jacComp q M') :
    σ • (diamondHBar (q ^ 2 * M') (levelH q M') d P) =
      diamondHBar (q ^ 2 * M') (levelH q M') d (σ • P) :=
  galois_smul_genOpH_comm (q ^ 2 * M') (levelH q M') (∅ : Set ℕ) σ (.dia d) P

theorem heckeGenJac_mul_galJac (σ : Gal) (ℓ : ℕ) :
    heckeGenJac q M' ℓ * galJac q M' σ = galJac q M' σ * heckeGenJac q M' ℓ := by
  by_cases h : ℓ.Prime ∧ ¬ ℓ ∣ q * M'
  · have hℓ := h.1
    have hℓqM := h.2
    have hq : ℓ.Coprime q := (Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hd => hℓqM (hd.mul_right M')
    have hqM : ℓ.Coprime (q ^ 2 * M') := by
      refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 hq) ?_
      exact (Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hd => hℓqM (hd.mul_left q)
    refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
    show (heckeGenJac q M' ℓ (galJac q M' σ x)).eval ζ = (galJac q M' σ (heckeGenJac q M' ℓ x)).eval ζ
    rw [heckeGenJac_eval hℓ hℓqM hq hqM, galJac_eval, galJac_eval, heckeGenJac_eval hℓ hℓqM hq hqM,
      smul_pow, smul_diamondHBar, smul_heckeOperatorHAlong σ hℓ]
  · have h0 : heckeGenJac q M' ℓ = 0 := by
      rw [heckeGenJac, dif_neg h]
    rw [h0, zero_mul, mul_zero]

theorem heckeJac_heckeGen_mul_galJac (σ : Gal) (ℓ : Nat.Primes) :
    heckeJac q M' (heckeGen ℓ) * galJac q M' σ = galJac q M' σ * heckeJac q M' (heckeGen ℓ) := by
  by_cases h : HeckeGenCommute q M'
  · rw [heckeJac_heckeGen h]
    exact heckeGenJac_mul_galJac σ ℓ
  · rw [heckeJac_heckeGen_of_not h, zero_mul, mul_zero]

theorem heckeJac_mul_galJac (σ : Gal) (t : HeckeAlg) :
    heckeJac q M' t * galJac q M' σ = galJac q M' σ * heckeJac q M' t := by
  induction t using MvPolynomial.induction_on with
  | C n =>
    rw [show (MvPolynomial.C n : HeckeAlg) = (n : HeckeAlg) from (eq_intCast MvPolynomial.C n),
      map_intCast]
    exact Int.cast_comm n _
  | add p p' hp hp' => rw [map_add, add_mul, mul_add, hp, hp']
  | mul_X p ℓ hp =>
    rw [map_mul, mul_assoc, show (MvPolynomial.X ℓ : HeckeAlg) = heckeGen ℓ from rfl,
      heckeJac_heckeGen_mul_galJac, ← mul_assoc, hp, mul_assoc]

end TateHeckeGalComm
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm.ModularCurve.FullLevel.TateHeckeGalComm"

end ModularCurve.FullLevel
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm.ModularCurve.FullLevel.TateHeckeGalComm P2MW.S_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm.ModularCurve P2MW.S_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm.ModularCurve.FullLevel.TateHeckeGalComm P2MW.S_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm.ModularCurve"

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime] :
    ∀ (t : ModularCurve.HeckeAlg) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ModularCurve.FullLevel.tateHecke q M' lam t * ModularCurve.FullLevel.tateGal q M' lam σ =
        ModularCurve.FullLevel.tateGal q M' lam σ * ModularCurve.FullLevel.tateHecke q M' lam t := by
  intro t σ
  show ModularCurve.FullLevel.tateEnd q M' lam (ModularCurve.FullLevel.heckeJac q M' t) *
      ModularCurve.FullLevel.tateEnd q M' lam (ModularCurve.FullLevel.galJac q M' σ) =
    ModularCurve.FullLevel.tateEnd q M' lam (ModularCurve.FullLevel.galJac q M' σ) *
      ModularCurve.FullLevel.tateEnd q M' lam (ModularCurve.FullLevel.heckeJac q M' t)
  rw [← map_mul, ← map_mul, ModularCurve.FullLevel.TateHeckeGalComm.heckeJac_mul_galJac]

end S_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm
end P2MW
export P2MW.S_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm (solution)
