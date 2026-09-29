-- Prove2me | solution 1 for MvFormalGroup.isCocomm_of_comul_eq_adicEval_toPowerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/753b0cc1-ebaa-5b2e-acf4-91a4ed9efa23

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_isCocomm_of_comul_eq_adicEval_toPowerSeries

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm IsComm.comm toPowerSeries constantCoeff_eq_zero adicEval adicEval_X adicEval_mem_radical adicEval_subst map_adicEval"
namespace CocommC12
p2m_open "MvFormalGroup"

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ)
  {S : Type*} [CommRing S] [Algebra 𝓞 S] {S' : Type*} [CommRing S'] [Algebra 𝓞 S']

private theorem map_mem_span (φ : S →ₐ[𝓞] S') {s : S} (hs : s ∈ Ideal.span {(p : S)}) :
    φ s ∈ Ideal.span {(p : S')} := by
  rw [Ideal.mem_span_singleton'] at hs ⊢
  obtain ⟨a, rfl⟩ := hs
  exact ⟨φ a, by rw [map_mul, map_natCast]⟩

private theorem map_mem_radical (φ : S →ₐ[𝓞] S') {s : S} (hs : s ∈ (Ideal.span {(p : S)}).radical) :
    φ s ∈ (Ideal.span {(p : S')}).radical := by
  obtain ⟨n, hn⟩ := hs
  exact ⟨n, by rw [← map_pow]; exact map_mem_span p φ hn⟩

end MvFormalGroup.CocommC12

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i)) :
    Coalgebra.IsCocomm 𝓞 R := by
  classical

  haveI : IsAdicComplete (Ideal.span {(p : R)}) R :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p R
  haveI : IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R ⊗[𝓞] R)
  let Δ : R →ₐ[𝓞] R ⊗[𝓞] R := Bialgebra.comulAlgHom 𝓞 R
  let σ : R ⊗[𝓞] R →ₐ[𝓞] R ⊗[𝓞] R := Algebra.TensorProduct.comm 𝓞 R R
  have hΔ : ∀ r, Δ r = Coalgebra.comul (R := 𝓞) r := fun _ => rfl
  have hJ : (Ideal.span {(p : R)}).FG := ⟨{(p : R)}, by simp⟩
  have hJ2 : (Ideal.span {(p : R ⊗[𝓞] R)}).FG := ⟨{(p : R ⊗[𝓞] R)}, by simp⟩

  have hfam : ∀ s, Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)) s ∈
      (Ideal.span {(p : R ⊗[𝓞] R)}).radical := by
    rintro (j | j)
    · exact MvFormalGroup.CocommC12.map_mem_radical p (Algebra.TensorProduct.includeLeft : R →ₐ[𝓞] R ⊗[𝓞] R)
        (hπX j)
    · exact MvFormalGroup.CocommC12.map_mem_radical p (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] R ⊗[𝓞] R)
        (hπX j)
  have hfam' : ∀ s, Sum.elim (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)) (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) s ∈
      (Ideal.span {(p : R ⊗[𝓞] R)}).radical := by
    rintro (j | j)
    · exact hfam (Sum.inr j)
    · exact hfam (Sum.inl j)
  have hΔX : ∀ i, Δ (π (X i)) ∈ (Ideal.span {(p : R ⊗[𝓞] R)}).radical := by
    intro i
    rw [hΔ, hπΔ i]
    exact MvFormalGroup.adicEval_mem_radical _ hfam (F.constantCoeff_eq_zero i)

  have h1 : ∀ G, Δ (π G) = MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)}) (fun i => Δ (π (X i))) G := by
    intro G
    rw [hπeval G]
    exact MvFormalGroup.map_adicEval _ _ Δ hJ
      (fun s hs => Ideal.le_radical (MvFormalGroup.CocommC12.map_mem_span p Δ hs)) hπX G
  have h2 : ∀ G, σ (Δ (π G)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)}) (fun i => σ (Δ (π (X i)))) G := by
    intro G
    rw [h1]
    exact MvFormalGroup.map_adicEval _ _ σ hJ2
      (fun s hs => Ideal.le_radical (MvFormalGroup.CocommC12.map_mem_span p σ hs)) hΔX G

  have h3 : ∀ i, σ (Δ (π (X i))) = Δ (π (X i)) := by
    intro i
    rw [hΔ, hπΔ i, MvFormalGroup.map_adicEval _ _ σ hJ2
      (fun s hs => Ideal.le_radical (MvFormalGroup.CocommC12.map_mem_span p σ hs)) hfam (F.toPowerSeries i)]
    have hswap : (fun s => σ (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)) s)) =
        Sum.elim (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)) (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) := by
      funext s
      rcases s with j | j
      · exact Algebra.TensorProduct.comm_tmul 𝓞 _ _
      · exact Algebra.TensorProduct.comm_tmul 𝓞 _ _
    rw [hswap]
    conv_rhs => rw [← MvFormalGroup.IsComm.comm (F := F) i]
    rw [MvFormalGroup.adicEval_subst _ hfam
      (hasSubst_of_constantCoeff_zero fun s => by rcases s with j | j <;> exact constantCoeff_X _)
      (F.toPowerSeries i)]
    congr 1
    funext s
    rcases s with j | j
    · simp only [Sum.elim_inl, MvFormalGroup.adicEval_X, Sum.elim_inr]
    · simp only [Sum.elim_inr, MvFormalGroup.adicEval_X, Sum.elim_inl]

  refine ⟨LinearMap.ext fun r => ?_⟩
  obtain ⟨G, rfl⟩ := hπ r
  change σ (Δ (π G)) = Δ (π G)
  rw [h2, h1]
  congr 1
  funext i
  exact h3 i

end S_MvFormalGroup_isCocomm_of_comul_eq_adicEval_toPowerSeries
end P2MW
export P2MW.S_MvFormalGroup_isCocomm_of_comul_eq_adicEval_toPowerSeries (solution)
