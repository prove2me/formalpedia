-- Prove2me | solution 1 for LatticePrepro.FieldSetup.exists_fieldSetup
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:15.089824+00:00
-- url     : https://prove2.me/submissions/ea961f00-a547-49a7-88eb-693c5f800dd2

import Mathlib
import Definitions.Def_LatticePrepro_Tables_FieldSetup

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.FieldSetup end LatticePrepro.FieldSetup

namespace LatticePrepro

namespace FieldSetup

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ}

/-- Field setups exist for every `d ≥ 1` and `δ ≥ 1` (take `𝕊 = 𝔽_{p^d}` and
`K = 𝔽_{p^{dδ}}`, with `γ` a primitive element of `K/𝕊`). -/
private theorem exists_fieldSetup (p : ℕ) [Fact p.Prime] (d δ : ℕ) (hd : 1 ≤ d) (hδ : 1 ≤ δ) :
    Nonempty (FieldSetup p d δ) := by
  classical
  have hd0 : d ≠ 0 := by omega
  have hdδ : d * δ ≠ 0 := Nat.mul_ne_zero hd0 (by omega)
  let 𝕊 := GaloisField p d
  let K := GaloisField p (d * δ)
  let : Fintype 𝕊 := Fintype.ofFinite _
  let : Fintype K := Fintype.ofFinite _
  -- the embedding `𝕊 → K`
  obtain ⟨φ⟩ : Nonempty (𝕊 →ₐ[ZMod p] K) := by
    apply FiniteField.nonempty_algHom_of_finrank_dvd
    rw [GaloisField.finrank p hd0, GaloisField.finrank p hdδ]
    exact Dvd.intro δ rfl
  let : Algebra 𝕊 K := φ.toRingHom.toAlgebra
  have : IsScalarTower (ZMod p) 𝕊 K :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  -- cardinalities and the degree `[K : 𝕊] = δ`
  have hcard𝕊 : Fintype.card 𝕊 = p ^ d := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p d hd0
  have hcardK : Fintype.card K = p ^ (d * δ) := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p (d * δ) hdδ
  have hfin : Module.finrank 𝕊 K = δ := by
    have h := Module.card_eq_pow_finrank (K := 𝕊) (V := K)
    rw [hcardK, hcard𝕊, ← pow_mul] at h
    have h2 := Nat.pow_right_injective (Fact.out : p.Prime).two_le h
    exact (Nat.eq_of_mul_eq_mul_left (by omega) h2).symm
  -- a power basis of `K` over `𝕊`
  let pb : PowerBasis 𝕊 K := Field.powerBasisOfFiniteOfSeparable 𝕊 K
  have hdim : pb.dim = δ := by rw [← pb.finrank, hfin]
  have hli : LinearIndependent 𝕊 (fun i : Fin δ => pb.gen ^ (i : ℕ)) := by
    have h := pb.basis.linearIndependent
    rw [pb.coe_basis] at h
    exact h.comp (finCongr hdim.symm) (finCongr hdim.symm).injective
  refine ⟨{ 𝕊 := 𝕊, card_𝕊 := hcard𝕊, K := K, γ := pb.gen, exists_aeval := ?_,
            linearIndependent_pow := hli }⟩
  intro x
  obtain ⟨f, hf, hx⟩ := pb.exists_eq_aeval x
  exact ⟨f, hdim ▸ hf, hx.symm⟩

variable (FS : FieldSetup p d δ)

end FieldSetup

end LatticePrepro

open LatticePrepro
open LatticePrepro.FieldSetup
variable {p : ℕ} [Fact p.Prime] {d δ : ℕ}
theorem solution (p : ℕ) [Fact p.Prime] (d δ : ℕ) (hd : 1 ≤ d) (hδ : 1 ≤ δ) :
    Nonempty (FieldSetup p d δ) :=
  @LatticePrepro.FieldSetup.exists_fieldSetup p _ d δ hd hδ
