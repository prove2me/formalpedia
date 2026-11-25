-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.indep_mul_genUp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:34:26.5117+00:00
-- url     : https://prove2.me/submissions/35235a3e-438a-47b5-8fdc-d595c9b1df33

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsBlockDiag_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsBlockDiag_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_generic_block_matrix_isBlockDiag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_generic_block_matrix_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_genUp_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_genUp_blockDiag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_genUp_upper
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_genLow_map
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_genUp_map
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_exists_univ_decomp
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
variable {R : Type} [CommRing R] {N : ℕ} {Ψ : Type}
variable {j : ℕ} {S : Type} [CommRing S]
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace IsGenericFlag
theorem _root_.solution {Ω Φ : Type} [Field Ω] [CommRing Φ] [Algebra Ω Φ]
    {g : Ψ → Matrix (Fin N) (Fin N) Φ} (hg : ∀ τ, IsBlockDiag j (g τ)) (h : IsGenericFlag Ω j g) :
    AlgebraicIndependent Ω fun q : inertBlockIndex Ψ N j =>
      ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2 := by
  obtain ⟨T, _, _, i, ψ', B', hi, -, hB'⟩ := exists_univ_decomp Ω Ψ N j
  obtain ⟨B, hB, h⟩ := h
  let A := MvPolynomial (LowIdx Ψ N j) Ω
  let θ : MvPolynomial (UpIdx Ψ N j) Φ →ₐ[Φ] MvPolynomial (UpIdx Ψ N j) Φ :=
    aeval fun q => ((B q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2
  have hθ : ∀ τ, (genUp Φ N j τ).map θ.toRingHom = (B τ).map C * genUp Φ N j τ :=
    genUp_map _ (fun τ => ⟨((hB τ).1.map _).mul (genUp_blockDiag τ), ((hB τ).2.1.map _).mul (genUp_upper τ)⟩)
      fun q => aeval_X _ q
  let ev : A →ₐ[Ω] Φ := aeval fun q => (g q.1.1 * B q.1.1) q.1.2.1 q.1.2.2
  have hev : ∀ τ, (genLow Ω N j τ).map ev.toRingHom = g τ * B τ :=
    genLow_map _ (fun τ => ⟨(hg τ).mul (hB τ).1, (hB τ).2.2⟩) fun q => aeval_X _ q
  let μ : MvPolynomial (UpIdx Ψ N j) A →ₐ[Ω] MvPolynomial (UpIdx Ψ N j) Φ := MvPolynomial.mapAlgHom ev
  have hμ : Function.Injective μ := MvPolynomial.map_injective ev.toRingHom h
  have hd : ∀ τ, IsUnit (B' τ).det := fun τ =>
    IsUnit.of_mul_eq_one_right _ (by rw [← det_mul, (hB' τ).2.2.1.det])
  let lo : A →ₐ[Ω] T := aeval fun q => ((genericBlockMatrix Ω N j q.1.1).map i.toRingHom * B' q.1.1) q.1.2.1 q.1.2.2
  have hlo : ∀ τ, (genLow Ω N j τ).map lo.toRingHom = (genericBlockMatrix Ω N j τ).map i.toRingHom * B' τ :=
    genLow_map _ (fun τ => ⟨((generic_block_matrix_isBlockDiag τ).map _).mul (hB' τ).1, (hB' τ).2.2.1⟩) fun q => aeval_X _ q
  let ν : MvPolynomial (UpIdx Ψ N j) A →ₐ[Ω] T := aevalTower lo fun q => (B' q.1.1)⁻¹ q.1.2.1 q.1.2.2
  have hν : ∀ τ, (genUp A N j τ).map ν.toRingHom = (B' τ)⁻¹ :=
    genUp_map _ (fun τ => ⟨(hB' τ).1.inv (hd τ), by
      letI := Matrix.invertibleOfIsUnitDet _ (hd τ)
      exact blockTriangular_inv_of_blockTriangular (hB' τ).2.1⟩) fun q => aevalTower_X _ _ q
  let Z : Ψ → Matrix (Fin N) (Fin N) (MvPolynomial (UpIdx Ψ N j) A) := fun τ =>
    (genLow Ω N j τ).map (C : A →+* _) * genUp A N j τ
  have h1 : AlgebraicIndependent Ω fun q : inertBlockIndex Ψ N j => Z q.1.1 q.1.2.1 q.1.2.2 := by
    refine AlgebraicIndependent.of_comp ν ?_
    convert (MvPolynomial.algebraicIndependent_X (inertBlockIndex Ψ N j) Ω).map' (f := i) hi using 1
    funext q
    have : (Z q.1.1).map ν.toRingHom = (genericBlockMatrix Ω N j q.1.1).map i.toRingHom := by
      rw [Matrix.map_mul, hν, show ((genLow Ω N j q.1.1).map (C : A →+* _)).map ν.toRingHom =
        (genLow Ω N j q.1.1).map lo.toRingHom from Matrix.ext fun a b => aevalTower_C _ _ _, hlo,
        Matrix.mul_nonsing_inv_cancel_right _ _ (hd _)]
    exact (congrFun (congrFun this _) _).trans (congrArg i (generic_block_matrix_apply q))
  refine AlgebraicIndependent.of_comp (θ.restrictScalars Ω) ?_
  convert h1.map' (f := μ) hμ using 1
  funext q
  have : ((g q.1.1).map C * genUp Φ N j q.1.1).map θ.toRingHom = (Z q.1.1).map μ.toRingHom := by
    rw [Matrix.map_mul, Matrix.map_mul, hθ, ← Matrix.mul_assoc,
      genUp_map μ.toRingHom (H := genUp Φ N j) (fun τ => ⟨genUp_blockDiag τ, genUp_upper τ⟩)
        (fun q => (map_X _ q).trans (genUp_apply q).symm),
      show ((g q.1.1).map C).map θ.toRingHom = (g q.1.1).map C from Matrix.ext fun a b => aeval_C _ _,
      ← Matrix.map_mul, ← hev]
    congr 1
    exact Matrix.ext fun a b => (MvPolynomial.map_C ev.toRingHom (genLow Ω N j q.1.1 a b)).symm
  exact congrFun (congrFun this _) _
end IsGenericFlag
end GlobalTheory.CompanionTheory.Ar.PB
