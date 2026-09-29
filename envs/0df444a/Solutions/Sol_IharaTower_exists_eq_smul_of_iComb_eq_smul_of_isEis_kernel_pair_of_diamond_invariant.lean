-- Prove2me | solution 1 for IharaTower.exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ca4182d6-15bc-52fd-9fa6-87fc088fae87

import Mathlib
import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_CohCarrier_Tower
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant

set_option autoImplicit false

p2m_open "CohCarrier IharaLemma IharaTower P2MW.S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant.IharaTower IharaTower.CornerData IharaTower.RungAssembly"

namespace IharaTower
p2m_export "IharaTower" "CornerData DegeneracyDescent DegeneracyDescent.toLegDatum_iLeg H1CornerData RungAssembly.iComb"
namespace ResidualInjectivity
p2m_open "IharaTower"

theorem exists_eq_smul_of_forall_mem_span {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {Γ : Type} [AddGroup Γ]
    {ϖ : 𝒪} (hϖ : ϖ ≠ 0) (θ : Γ →+ 𝒪) (hθ : ∀ γ, θ γ ∈ Ideal.span ({ϖ} : Set 𝒪)) :
    ∃ ψ : Γ →+ 𝒪, θ = ϖ • ψ := by
  have hex : ∀ γ, ∃ a, θ γ = ϖ * a := fun γ => by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (hθ γ)
    exact ⟨a, by rw [← ha, mul_comm]⟩
  choose f hf using hex
  refine ⟨⟨⟨f, ?_⟩, ?_⟩, ?_⟩
  · apply mul_left_cancel₀ hϖ
    rw [← hf, map_zero, mul_zero]
  · intro γ δ
    apply mul_left_cancel₀ hϖ
    rw [← hf, map_add, hf, hf, mul_add]
  · ext γ
    show θ γ = ϖ • f γ
    rw [hf, smul_eq_mul]

section Reduction

variable {𝒪 : Type} [CommRing 𝒪] (ϖ : 𝒪) (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def red : H1 M H 𝒪 →+ H1 M H (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) :=
  AddMonoidHom.compHom ((Ideal.Quotient.mk (Ideal.span ({ϖ} : Set 𝒪))).toAddMonoidHom)

@[scoped simp] theorem red_apply (φ : H1 M H 𝒪) (x : Additive ↥(GammaH M H)) :
    red ϖ M H φ x = Ideal.Quotient.mk (Ideal.span ({ϖ} : Set 𝒪)) (φ x) := rfl

theorem red_smul (a : 𝒪) (φ : H1 M H 𝒪) : red ϖ M H (a • φ) = a • red ϖ M H φ := by
  refine AddMonoidHom.ext fun x => ?_
  show Ideal.Quotient.mk (Ideal.span ({ϖ} : Set 𝒪)) (a • φ x) = a • Ideal.Quotient.mk (Ideal.span ({ϖ} : Set 𝒪)) (φ x)
  rw [smul_eq_mul, map_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]

theorem red_varpi_smul (φ : H1 M H 𝒪) : red ϖ M H (ϖ • φ) = 0 := by
  refine AddMonoidHom.ext fun x => ?_
  show Ideal.Quotient.mk (Ideal.span ({ϖ} : Set 𝒪)) (ϖ • φ x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)

theorem exists_eq_smul_of_red_eq_zero [IsDomain 𝒪] (hϖ : ϖ ≠ 0) (φ : H1 M H 𝒪) (h : red ϖ M H φ = 0) :
    ∃ ψ : H1 M H 𝒪, φ = ϖ • ψ :=
  exists_eq_smul_of_forall_mem_span hϖ φ fun γ => by
    have hγ : Ideal.Quotient.mk (Ideal.span ({ϖ} : Set 𝒪)) (φ γ) = 0 := DFunLike.congr_fun h γ
    exact Ideal.Quotient.eq_zero_iff_mem.mp hγ

variable {M H}

theorem iDeg'_red {M' : ℕ} {H' : Subgroup (ZMod M')ˣ} [NeZero M'] {d : ℕ} [NeZero d] (hle : LevelLE M M' H H' d)
    (φ : H1 M H 𝒪) :
    iDeg' M M' H H' d (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) hle (red ϖ M H φ) = red ϖ M' H' (iDeg' M M' H H' d 𝒪 hle φ) := rfl

theorem diamondRaw_red (σ : CongruenceSubgroup.Gamma0 M) (φ : H1 M H 𝒪) :
    diamondRaw M H (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) σ (red ϖ M H φ) = red ϖ M H (diamondRaw M H 𝒪 σ φ) := rfl

theorem heckeT_red (ℓ : ℕ) [NeZero ℓ] (φ : H1 M H 𝒪) :
    heckeT M H ℓ (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) (red ϖ M H φ) = red ϖ M H (heckeT M H ℓ 𝒪 φ) :=
  CohCarrier.heckeT_comp_coeff M H ℓ _ φ

end Reduction

end IharaTower.ResidualInjectivity
p2m_reactivate "P2MW.S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant.IharaTower P2MW.S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant.IharaTower.ResidualInjectivity"
p2m_reactivate "P2MW.S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant.IharaTower"

open IharaTower.ResidualInjectivity in

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)] (hq : q.Prime) (hqN : ¬ q ∣ N)
    {H : Subgroup (ZMod N)ˣ} {H' : Subgroup (ZMod (N * q))ˣ}
    (h₁ : CohCarrier.LevelLE N (N * q) H H' 1) (hq' : CohCarrier.LevelLE N (N * q) H H' q)
    {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
    [Module 𝕋 (CohCarrier.H1 N H 𝒪)] [Module 𝕋' (CohCarrier.H1 (N * q) H' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (CohCarrier.H1 N H 𝒪)] [IsScalarTower 𝒪 𝕋' (CohCarrier.H1 (N * q) H' 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N H 𝒪 𝕋) (cd' : H1CornerData (𝒪 := 𝒪) (N * q) H' 𝒪 𝕋')
    (D : DegeneracyDescent (𝒪 := 𝒪) cd cd' 2)
    (hD : D.iRaw = ![CohCarrier.iDegL N (N * q) H H' 1 𝒪 𝒪 h₁, CohCarrier.iDegL N (N * q) H H' q 𝒪 𝒪 hq'])
    (table : Fin 2 → Fin 2 → cd.cornerRing)
    (adjoint_leg : ∀ (k : Fin 2) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B (D.jLeg k m') m = cd'.pairing.B m' (D.iLeg k m))
    (htable : ∀ (k k' : Fin 2) (m : cd.cornerModule), D.jLeg k (D.iLeg k' m) = table k k' • m)
    (c : Fin 2 → cd.cornerRing)
    [Module.Free 𝒪 cd.cornerModule] [Module.Free 𝒪 cd'.cornerModule]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)

    (hc : ∀ v : cd.cornerModule, (∀ k, ∃ w : cd.cornerModule, c k • v = ϖ • w) → ∃ v₁, v = ϖ • v₁)

    (ℓ₀ : ℕ) [NeZero ℓ₀] (hℓ : ℓ₀.Prime) (hℓN : ¬ ℓ₀ ∣ N * q)
    (hne : ∀ v : cd.cornerModule,
      CohCarrier.heckeT N H ℓ₀ 𝒪 (v : CohCarrier.H1 N H 𝒪) - ((ℓ₀ : 𝒪) + 1) • (v : CohCarrier.H1 N H 𝒪)
        ∈ (Ideal.span {ϖ} • ⊤ : Submodule 𝒪 (CohCarrier.H1 N H 𝒪)) → ∃ v₁ : cd.cornerModule, v = ϖ • v₁)

    (hihara : ∀ g h : CohCarrier.H1 N H (𝒪 ⧸ Ideal.span {ϖ}),
      (∀ σ : CongruenceSubgroup.Gamma0 N, CohCarrier.diamondRaw N H (𝒪 ⧸ Ideal.span {ϖ}) σ g = g) →
      (∀ σ : CongruenceSubgroup.Gamma0 N, CohCarrier.diamondRaw N H (𝒪 ⧸ Ideal.span {ϖ}) σ h = h) →
      CohCarrier.iDeg' N (N * q) H H' 1 (𝒪 ⧸ Ideal.span {ϖ}) h₁ g +
          CohCarrier.iDeg' N (N * q) H H' q (𝒪 ⧸ Ideal.span {ϖ}) hq' h = 0 →
        CohCarrier.IsEis 𝒪 (𝒪 ⧸ Ideal.span {ϖ}) N H ℓ₀ g ∧ CohCarrier.IsEis 𝒪 (𝒪 ⧸ Ideal.span {ϖ}) N H ℓ₀ h)

    (hdia : ∀ (σ : CongruenceSubgroup.Gamma0 N) (v : cd.cornerModule),
      CohCarrier.diamondRaw N H 𝒪 σ (v : CohCarrier.H1 N H 𝒪) = (v : CohCarrier.H1 N H 𝒪)) :
    ∀ (v : cd.cornerModule) (x : cd'.cornerModule),
      RungAssembly.iComb (D.toLegDatum table adjoint_leg htable) c v = ϖ • x → ∃ v₁, v = ϖ • v₁ := by
  intro v x hvx
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero

  let w : Fin 2 → cd.cornerModule := fun k => c k • v

  have hi : ∀ (k : Fin 2) (u : cd.cornerModule), (D.iLeg k u : CohCarrier.H1 (N * q) H' 𝒪) =
      ![CohCarrier.iDegL N (N * q) H H' 1 𝒪 𝒪 h₁, CohCarrier.iDegL N (N * q) H H' q 𝒪 𝒪 hq'] k u := fun k u => by
    simp [hD]
  have e1 : CohCarrier.iDeg' N (N * q) H H' 1 𝒪 h₁ (w 0 : CohCarrier.H1 N H 𝒪) +
      CohCarrier.iDeg' N (N * q) H H' q 𝒪 hq' (w 1 : CohCarrier.H1 N H 𝒪) =
      ϖ • (x : CohCarrier.H1 (N * q) H' 𝒪) := by
    have := congrArg (fun z : cd'.cornerModule => (z : CohCarrier.H1 (N * q) H' 𝒪)) hvx
    simp [iComb, Fin.sum_univ_two, DegeneracyDescent.toLegDatum_iLeg, hi, w] at this
    exact this

  have hker : CohCarrier.iDeg' N (N * q) H H' 1 (𝒪 ⧸ Ideal.span {ϖ}) h₁ (red ϖ N H (w 0 : CohCarrier.H1 N H 𝒪)) +
      CohCarrier.iDeg' N (N * q) H H' q (𝒪 ⧸ Ideal.span {ϖ}) hq' (red ϖ N H (w 1 : CohCarrier.H1 N H 𝒪)) = 0 := by
    rw [iDeg'_red, iDeg'_red, ← map_add, e1, red_varpi_smul]
  have hinv : ∀ (k : Fin 2) (σ : CongruenceSubgroup.Gamma0 N),
      CohCarrier.diamondRaw N H (𝒪 ⧸ Ideal.span {ϖ}) σ (red ϖ N H (w k : CohCarrier.H1 N H 𝒪)) =
        red ϖ N H (w k : CohCarrier.H1 N H 𝒪) := fun k σ => by
    rw [diamondRaw_red, hdia σ (w k)]
  obtain ⟨hE0, hE1⟩ := hihara _ _ (hinv 0) (hinv 1) hker

  have hmem : ∀ k : Fin 2, CohCarrier.IsEis 𝒪 (𝒪 ⧸ Ideal.span {ϖ}) N H ℓ₀ (red ϖ N H (w k : CohCarrier.H1 N H 𝒪)) →
      CohCarrier.heckeT N H ℓ₀ 𝒪 (w k : CohCarrier.H1 N H 𝒪) - ((ℓ₀ : 𝒪) + 1) • (w k : CohCarrier.H1 N H 𝒪)
        ∈ (Ideal.span {ϖ} • ⊤ : Submodule 𝒪 (CohCarrier.H1 N H 𝒪)) := by
    intro k hk
    rw [CohCarrier.IsEis, heckeT_red, ← red_smul, ← sub_eq_zero, ← map_sub] at hk
    obtain ⟨ψ, hψ⟩ := exists_eq_smul_of_red_eq_zero ϖ N H hϖ0 _ hk
    rw [hψ]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) Submodule.mem_top

  obtain ⟨u0, hu0⟩ := hne (w 0) (hmem 0 hE0)
  obtain ⟨u1, hu1⟩ := hne (w 1) (hmem 1 hE1)
  exact hc v (Fin.forall_fin_two.mpr ⟨⟨u0, hu0⟩, ⟨u1, hu1⟩⟩)

end S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant
end P2MW
export P2MW.S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant (solution)
