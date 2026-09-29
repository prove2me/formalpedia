-- Prove2me | solution 1 for MvFormalGroup.exists_hopfAlgebra_surjective_ker_eq_span_nthSeries_comul_eq_adicEval_bot_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f2b625eb-3fd6-500c-badd-ac3f61234186

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_hopfAlgebra_surjective_ker_eq_span_nthSeries_comul_eq_adicEval_bot_of_isNilpotent

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open MvPowerSeries Function

universe u

namespace HopfQuot

variable {𝓞 : Type u} [CommRing 𝓞]

section Gen

private theorem map_span_le_radical {B C : Type*} [CommRing B] [Algebra 𝓞 B] [CommRing C] [Algebra 𝓞 C]
    (f : B →ₐ[𝓞] C) : ∀ s ∈ (⊥ : Ideal B), f s ∈ ((⊥ : Ideal C)).radical := by
  intro s hs
  rw [Submodule.mem_bot] at hs
  subst hs
  rw [map_zero]
  exact Ideal.zero_mem _

private theorem map_mem_radical {B C : Type*} [CommRing B] [Algebra 𝓞 B] [CommRing C] [Algebra 𝓞 C]
    (f : B →ₐ[𝓞] C) {b : B} (hb : b ∈ ((⊥ : Ideal B)).radical) :
    f b ∈ ((⊥ : Ideal C)).radical := by
  obtain ⟨n, hn⟩ := hb
  refine ⟨n, ?_⟩
  rw [Submodule.mem_bot] at hn
  rw [← map_pow, hn, map_zero]
  exact Ideal.zero_mem _

private theorem fg_span (B : Type*) [CommRing B] : ((⊥ : Ideal B)).FG := Submodule.fg_bot

end Gen

section Level

variable {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm] (n : ℕ)
  {L : Type u} [CommRing L] [Algebra 𝓞 L] [Module.Finite 𝓞 L] [Module.Free 𝓞 L]
  (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L) (hπ : Surjective π) (hX : ∀ i, IsNilpotent (π (X i)))
  (hker : RingHom.ker π = Ideal.span (Set.range (Φ.nthSeries n)))

include hX in
omit [Φ.IsComm] [Module.Finite 𝓞 L] [Module.Free 𝓞 L] in

private theorem X_mem_radical (i : Fin d) : π (X i) ∈ ((⊥ : Ideal L)).radical := by
  obtain ⟨k, hk⟩ := hX i
  exact ⟨k, by rw [hk]; exact Ideal.zero_mem _⟩

include hX in
omit [Φ.IsComm] in

private theorem π_eq_adicEval (G : MvPowerSeries (Fin d) 𝓞) :
    π G = MvFormalGroup.adicEval ((⊥ : Ideal L)) (fun i => π (X i)) G :=
  MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical _ π (X_mem_radical π hX) G

private noncomputable def ξ : MvFormalGroup.Points Φ L ((⊥ : Ideal L)) :=
  ⟨fun i => π (X i), X_mem_radical π hX⟩

omit [Φ.IsComm] [Module.Free 𝓞 L] in
private theorem ξ_val (i : Fin d) : (ξ Φ π hX).val i = π (X i) := rfl

include hker in
omit [Φ.IsComm] in

private theorem nsmul_ξ : n • ξ Φ π hX = 0 := by
  ext i
  rw [MvFormalGroup.Points.val_nsmul, MvFormalGroup.Points.val_zero]
  change MvFormalGroup.adicEval _ (fun i => π (X i)) (Φ.nthSeries n i) = 0
  rw [← π_eq_adicEval π hX, ← RingHom.mem_ker, hker]
  exact Ideal.subset_span ⟨i, rfl⟩

omit [Φ.IsComm] [Module.Finite 𝓞 L] [Module.Free 𝓞 L] in
include hπ in

private theorem algHom_ext {T : Type*} [Semiring T] [Algebra 𝓞 T] {f g : L →ₐ[𝓞] T}
    (h : ∀ a, f (π a) = g (π a)) : f = g := by
  refine AlgHom.ext fun y => ?_
  obtain ⟨a, rfl⟩ := hπ y
  exact h a

private noncomputable def descend {T : Type*} [CommRing T] [Algebra 𝓞 T] (ψ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] T)
    (h : ∀ a, π a = 0 → ψ a = 0) : L →ₐ[𝓞] T :=
  (Ideal.Quotient.liftₐ (RingHom.ker π) ψ fun a ha => h a ha).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom

omit [Φ.IsComm] [Module.Finite 𝓞 L] [Module.Free 𝓞 L] in
private theorem descend_apply {T : Type*} [CommRing T] [Algebra 𝓞 T] (ψ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] T)
    (h : ∀ a, π a = 0 → ψ a = 0) (a : MvPowerSeries (Fin d) 𝓞) : descend π hπ ψ h (π a) = ψ a := by
  rw [descend, AlgHom.comp_apply]
  have : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom (π a) = Ideal.Quotient.mk (RingHom.ker π) a := by
    rw [AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

private abbrev P (T : Type*) [CommRing T] := MvFormalGroup.Points Φ T ((⊥ : Ideal T))

private noncomputable def mp {T T' : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    [CommRing T'] [Algebra 𝓞 T'] [IsAdicComplete ((⊥ : Ideal T')) T'] (φ : T →ₐ[𝓞] T') :
    P Φ T →+ P Φ T' :=
  MvFormalGroup.Points.map φ (fg_span T) (map_span_le_radical φ)

private noncomputable def ptOf {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    (φ : L →ₐ[𝓞] T) : P Φ T := mp Φ φ (ξ Φ π hX)

omit [Φ.IsComm] in
private theorem ptOf_val {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    (φ : L →ₐ[𝓞] T) (j : Fin d) : (ptOf Φ π hX φ).val j = φ (π (X j)) := rfl

omit [Φ.IsComm] in
private theorem mp_ptOf {T T' : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    [CommRing T'] [Algebra 𝓞 T'] [IsAdicComplete ((⊥ : Ideal T')) T'] (ψ : T →ₐ[𝓞] T') (φ : L →ₐ[𝓞] T) :
    mp Φ ψ (ptOf Φ π hX φ) = ptOf Φ π hX (ψ.comp φ) := by
  ext j; rfl

omit [Φ.IsComm] in

private theorem ptOf_congr {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    {φ φ' : L →ₐ[𝓞] T} (h : ∀ j, φ (π (X j)) = φ' (π (X j))) : ptOf Φ π hX φ = ptOf Φ π hX φ' := by
  ext j; exact h j

private theorem apply_val_add {T T' : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    [CommRing T'] [Algebra 𝓞 T'] [IsAdicComplete ((⊥ : Ideal T')) T'] (ψ : T →ₐ[𝓞] T')
    (u v : P Φ T) (i : Fin d) : ψ ((u + v).val i) = (mp Φ ψ u + mp Φ ψ v).val i := by
  rw [← map_add]; rfl

omit [Φ.IsComm] in
private theorem apply_val {T T' : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    [CommRing T'] [Algebra 𝓞 T'] [IsAdicComplete ((⊥ : Ideal T')) T'] (ψ : T →ₐ[𝓞] T')
    (u : P Φ T) (i : Fin d) : ψ (u.val i) = (mp Φ ψ u).val i := rfl

private noncomputable def a₁ : P Φ (L ⊗[𝓞] L) :=
  ptOf Φ π hX (Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L)
private noncomputable def a₂ : P Φ (L ⊗[𝓞] L) :=
  ptOf Φ π hX (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L)

omit [Φ.IsComm] in
private theorem a₁_val (j : Fin d) : (a₁ Φ π hX).val j = π (X j) ⊗ₜ[𝓞] (1 : L) := rfl
omit [Φ.IsComm] in
private theorem a₂_val (j : Fin d) : (a₂ Φ π hX).val j = (1 : L) ⊗ₜ[𝓞] π (X j) := rfl

omit [Φ.IsComm] in
private theorem mp_a₁ {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    (ψ : L ⊗[𝓞] L →ₐ[𝓞] T) :
    mp Φ ψ (a₁ Φ π hX) = ptOf Φ π hX (ψ.comp (Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L)) := by
  ext j; rfl
omit [Φ.IsComm] in
private theorem mp_a₂ {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    (ψ : L ⊗[𝓞] L →ₐ[𝓞] T) :
    mp Φ ψ (a₂ Φ π hX) = ptOf Φ π hX (ψ.comp (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L)) := by
  ext j; rfl

private noncomputable def Δ₀ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L ⊗[𝓞] L :=
  MvFormalGroup.adicEvalAlgHom ((⊥ : Ideal (L ⊗[𝓞] L))) (a₁ Φ π hX + a₂ Φ π hX).mem_radical

private theorem Δ₀_apply (G : MvPowerSeries (Fin d) 𝓞) :
    Δ₀ Φ π hX G = MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L))) (a₁ Φ π hX + a₂ Φ π hX).val G := by
  rw [Δ₀, MvFormalGroup.coe_adicEvalAlgHom]

include hker in

private theorem Δ₀_vanish (G : MvPowerSeries (Fin d) 𝓞) (hG : π G = 0) : Δ₀ Φ π hX G = 0 := by
  rw [← RingHom.mem_ker, hker] at hG
  have hle : Ideal.span (Set.range (Φ.nthSeries n)) ≤ RingHom.ker (Δ₀ Φ π hX) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, Δ₀_apply]
    have h := congrFun (MvFormalGroup.Points.val_nsmul n (a₁ Φ π hX + a₂ Φ π hX)) i
    rw [← h, nsmul_add, a₁, a₂, ptOf, ptOf, ← map_nsmul, ← map_nsmul, nsmul_ξ Φ n π hX hker, map_zero, map_zero,
      add_zero, MvFormalGroup.Points.val_zero]
  exact hle hG

private noncomputable def Δ : L →ₐ[𝓞] L ⊗[𝓞] L := descend π hπ (Δ₀ Φ π hX) (Δ₀_vanish Φ n π hX hker)

private theorem Δ_π (G : MvPowerSeries (Fin d) 𝓞) : Δ Φ n π hπ hX hker (π G) = Δ₀ Φ π hX G := descend_apply π hπ _ _ G

private theorem Δ_πX (i : Fin d) : Δ Φ n π hπ hX hker (π (X i)) = (a₁ Φ π hX + a₂ Φ π hX).val i := by
  rw [Δ_π, Δ₀_apply, MvFormalGroup.adicEval_X]

private theorem ptOf_Δ : ptOf Φ π hX (Δ Φ n π hπ hX hker) = a₁ Φ π hX + a₂ Φ π hX := by
  ext i; exact Δ_πX Φ n π hπ hX hker i

private noncomputable def ε₀ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] 𝓞 :=
  { MvPowerSeries.constantCoeff with commutes' := fun c => MvPowerSeries.constantCoeff_C c }

private theorem ε₀_apply (G : MvPowerSeries (Fin d) 𝓞) : ε₀ (𝓞 := 𝓞) (d := d) G = MvPowerSeries.constantCoeff G := rfl

include hker in
private theorem ε₀_vanish (G : MvPowerSeries (Fin d) 𝓞) (hG : π G = 0) : ε₀ G = 0 := by
  rw [← RingHom.mem_ker, hker] at hG
  have hle : Ideal.span (Set.range (Φ.nthSeries n)) ≤ RingHom.ker (ε₀ (𝓞 := 𝓞) (d := d)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact MvFormalGroup.constantCoeff_nthSeries Φ n i
  exact hle hG

private noncomputable def ε : L →ₐ[𝓞] 𝓞 := descend π hπ ε₀ (ε₀_vanish Φ n π hker)

private theorem ε_π (G : MvPowerSeries (Fin d) 𝓞) : ε Φ n π hπ hker (π G) = MvPowerSeries.constantCoeff G :=
  descend_apply π hπ _ _ G

private theorem ε_πX (i : Fin d) : ε Φ n π hπ hker (π (X i)) = 0 := by rw [ε_π, constantCoeff_X]

private noncomputable def S₀ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L :=
  MvFormalGroup.adicEvalAlgHom ((⊥ : Ideal L)) (-ξ Φ π hX).mem_radical

private theorem S₀_apply (G : MvPowerSeries (Fin d) 𝓞) :
    S₀ Φ π hX G = MvFormalGroup.adicEval ((⊥ : Ideal L)) (-ξ Φ π hX).val G := by
  rw [S₀, MvFormalGroup.coe_adicEvalAlgHom]

include hker in
private theorem S₀_vanish (G : MvPowerSeries (Fin d) 𝓞) (hG : π G = 0) : S₀ Φ π hX G = 0 := by
  rw [← RingHom.mem_ker, hker] at hG
  have hle : Ideal.span (Set.range (Φ.nthSeries n)) ≤ RingHom.ker (S₀ Φ π hX) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, S₀_apply]
    have h := congrFun (MvFormalGroup.Points.val_nsmul n (-ξ Φ π hX)) i
    rw [← h, smul_neg, nsmul_ξ Φ n π hX hker, neg_zero, MvFormalGroup.Points.val_zero]
  exact hle hG

include hπ in
private theorem algHom_ext_pt {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    {f g : L →ₐ[𝓞] T} (U V : P Φ T) (hU : ∀ i, f (π (X i)) = U.val i) (hV : ∀ i, g (π (X i)) = V.val i)
    (hUV : U = V) : f = g := by
  subst hUV
  refine algHom_ext π hπ fun G => ?_
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply,
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical ((⊥ : Ideal T)) (f.comp π)
      (fun i => by rw [AlgHom.comp_apply, hU]; exact U.mem_radical i) G,
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical ((⊥ : Ideal T)) (g.comp π)
      (fun i => by rw [AlgHom.comp_apply, hV]; exact U.mem_radical i) G]
  congr 1
  funext i
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hU, hV]

private theorem ptOf_eq_zero {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    {φ : L →ₐ[𝓞] T} (h : ∀ j, φ (π (X j)) = 0) : ptOf Φ π hX φ = 0 := by
  ext j; exact h j

private theorem ptOf_id : ptOf Φ π hX (AlgHom.id 𝓞 L) = ξ Φ π hX := by
  ext j; rfl

private theorem ptOf_comp_Δ {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    (φ : L ⊗[𝓞] L →ₐ[𝓞] T) :
    ptOf Φ π hX (φ.comp (Δ Φ n π hπ hX hker)) =
      ptOf Φ π hX (φ.comp (Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L)) +
        ptOf Φ π hX (φ.comp (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L)) := by
  rw [← mp_ptOf, ptOf_Δ, map_add, mp_a₁, mp_a₂]

section Axioms

private theorem coassoc :
    (Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 L L L).toAlgHom.comp
        ((Algebra.TensorProduct.map (Δ Φ n π hπ hX hker) (AlgHom.id 𝓞 L)).comp (Δ Φ n π hπ hX hker)) =
      (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (Δ Φ n π hπ hX hker)).comp (Δ Φ n π hπ hX hker) := by
  refine algHom_ext_pt Φ π hπ
    (mp Φ (Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 L L L).toAlgHom
      (mp Φ (Algebra.TensorProduct.map (Δ Φ n π hπ hX hker) (AlgHom.id 𝓞 L)) (a₁ Φ π hX) +
        mp Φ (Algebra.TensorProduct.map (Δ Φ n π hπ hX hker) (AlgHom.id 𝓞 L)) (a₂ Φ π hX)))
    (mp Φ (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (Δ Φ n π hπ hX hker)) (a₁ Φ π hX) +
      mp Φ (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (Δ Φ n π hπ hX hker)) (a₂ Φ π hX))
    (fun i => ?_) (fun i => ?_) ?_
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, Δ_πX]
    exact (congrArg _ (apply_val_add Φ _ _ _ i)).trans (apply_val Φ _ _ i)
  · rw [AlgHom.comp_apply, Δ_πX]
    exact apply_val_add Φ _ _ _ i
  ·
    rw [map_add, mp_a₁, mp_a₂, mp_a₁, mp_a₂, Algebra.TensorProduct.map_comp_includeLeft,
      Algebra.TensorProduct.map_comp_includeRight, Algebra.TensorProduct.map_comp_includeLeft,
      Algebra.TensorProduct.map_comp_includeRight, ptOf_comp_Δ, map_add, mp_ptOf, mp_ptOf, mp_ptOf,
      AlgHom.comp_id, AlgHom.comp_id, ptOf_comp_Δ, add_assoc]

    congr 1

private theorem rTensor_counit :
    (Algebra.TensorProduct.map (ε Φ n π hπ hker) (AlgHom.id 𝓞 L)).comp (Δ Φ n π hπ hX hker) =
      (Algebra.TensorProduct.lid 𝓞 L).symm.toAlgHom := by
  refine algHom_ext_pt Φ π hπ
    (mp Φ (Algebra.TensorProduct.map (ε Φ n π hπ hker) (AlgHom.id 𝓞 L)) (a₁ Φ π hX) +
      mp Φ (Algebra.TensorProduct.map (ε Φ n π hπ hker) (AlgHom.id 𝓞 L)) (a₂ Φ π hX))
    (ptOf Φ π hX (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] 𝓞 ⊗[𝓞] L))
    (fun i => ?_) (fun i => rfl) ?_
  · rw [AlgHom.comp_apply, Δ_πX]
    exact apply_val_add Φ _ _ _ i
  · rw [mp_a₁, mp_a₂, Algebra.TensorProduct.map_comp_includeLeft, Algebra.TensorProduct.map_comp_includeRight,
      AlgHom.comp_id, ptOf_eq_zero Φ π hX (fun j => by rw [AlgHom.comp_apply, ε_πX, map_zero]), zero_add]

private theorem lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (ε Φ n π hπ hker)).comp (Δ Φ n π hπ hX hker) =
      (Algebra.TensorProduct.rid 𝓞 𝓞 L).symm.toAlgHom := by
  refine algHom_ext_pt Φ π hπ
    (mp Φ (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (ε Φ n π hπ hker)) (a₁ Φ π hX) +
      mp Φ (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (ε Φ n π hπ hker)) (a₂ Φ π hX))
    (ptOf Φ π hX (Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] 𝓞))
    (fun i => ?_) (fun i => rfl) ?_
  · rw [AlgHom.comp_apply, Δ_πX]
    exact apply_val_add Φ _ _ _ i
  · rw [mp_a₁, mp_a₂, Algebra.TensorProduct.map_comp_includeLeft, Algebra.TensorProduct.map_comp_includeRight,
      AlgHom.comp_id,
      ptOf_eq_zero Φ π hX (φ := (Algebra.TensorProduct.includeRight : 𝓞 →ₐ[𝓞] L ⊗[𝓞] 𝓞).comp (ε Φ n π hπ hker))
        (fun j => by rw [AlgHom.comp_apply, ε_πX, map_zero]), add_zero]

@[reducible] private noncomputable def bialgebra : Bialgebra 𝓞 L :=
  Bialgebra.ofAlgHom (Δ Φ n π hπ hX hker) (ε Φ n π hπ hker) (coassoc Φ n π hπ hX hker)
    (rTensor_counit Φ n π hπ hX hker) (lTensor_counit Φ n π hπ hX hker)

private noncomputable def S : L →ₐ[𝓞] L := descend π hπ (S₀ Φ π hX) (S₀_vanish Φ n π hX hker)

private theorem S_π (G : MvPowerSeries (Fin d) 𝓞) : S Φ n π hπ hX hker (π G) = S₀ Φ π hX G := descend_apply π hπ _ _ G

private theorem ptOf_S : ptOf Φ π hX (S Φ n π hπ hX hker) = -ξ Φ π hX := by
  ext j
  rw [ptOf_val, S_π, S₀_apply, MvFormalGroup.adicEval_X]

private theorem antipode_right :
    (Algebra.TensorProduct.lmul' 𝓞 (S := L)).comp
        ((Algebra.TensorProduct.map (S Φ n π hπ hX hker) (AlgHom.id 𝓞 L)).comp (Δ Φ n π hπ hX hker)) =
      (Algebra.ofId 𝓞 L).comp (ε Φ n π hπ hker) := by
  refine algHom_ext_pt Φ π hπ
    (mp Φ (Algebra.TensorProduct.lmul' 𝓞 (S := L))
      (mp Φ (Algebra.TensorProduct.map (S Φ n π hπ hX hker) (AlgHom.id 𝓞 L)) (a₁ Φ π hX) +
        mp Φ (Algebra.TensorProduct.map (S Φ n π hπ hX hker) (AlgHom.id 𝓞 L)) (a₂ Φ π hX)))
    (0 : P Φ L) (fun i => ?_) (fun i => ?_) ?_
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, Δ_πX]
    exact (congrArg _ (apply_val_add Φ _ _ _ i)).trans (apply_val Φ _ _ i)
  · rw [AlgHom.comp_apply, ε_πX, map_zero, MvFormalGroup.Points.val_zero]
  · rw [map_add, mp_a₁, mp_a₂, Algebra.TensorProduct.map_comp_includeLeft,
      Algebra.TensorProduct.map_comp_includeRight, mp_ptOf, mp_ptOf, AlgHom.comp_id]
    have h1 : ptOf Φ π hX ((Algebra.TensorProduct.lmul' 𝓞 (S := L)).comp
        ((Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L).comp (S Φ n π hπ hX hker))) = -ξ Φ π hX := by
      rw [← ptOf_S Φ n π hπ hX hker]
      exact ptOf_congr Φ π hX fun j => by
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.lmul'_apply_tmul,
          mul_one]
    have h2 : ptOf Φ π hX ((Algebra.TensorProduct.lmul' 𝓞 (S := L)).comp
        (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L)) = ξ Φ π hX := by
      rw [← ptOf_id Φ π hX]
      exact ptOf_congr Φ π hX fun j => by
        simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.lmul'_apply_tmul, one_mul]
    rw [h1, h2, neg_add_cancel]

private theorem antipode_left :
    (Algebra.TensorProduct.lmul' 𝓞 (S := L)).comp
        ((Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (S Φ n π hπ hX hker)).comp (Δ Φ n π hπ hX hker)) =
      (Algebra.ofId 𝓞 L).comp (ε Φ n π hπ hker) := by
  refine algHom_ext_pt Φ π hπ
    (mp Φ (Algebra.TensorProduct.lmul' 𝓞 (S := L))
      (mp Φ (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (S Φ n π hπ hX hker)) (a₁ Φ π hX) +
        mp Φ (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (S Φ n π hπ hX hker)) (a₂ Φ π hX)))
    (0 : P Φ L) (fun i => ?_) (fun i => ?_) ?_
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, Δ_πX]
    exact (congrArg _ (apply_val_add Φ _ _ _ i)).trans (apply_val Φ _ _ i)
  · rw [AlgHom.comp_apply, ε_πX, map_zero, MvFormalGroup.Points.val_zero]
  · rw [map_add, mp_a₁, mp_a₂, Algebra.TensorProduct.map_comp_includeLeft,
      Algebra.TensorProduct.map_comp_includeRight, mp_ptOf, mp_ptOf, AlgHom.comp_id]
    have h1 : ptOf Φ π hX ((Algebra.TensorProduct.lmul' 𝓞 (S := L)).comp
        (Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L)) = ξ Φ π hX := by
      rw [← ptOf_id Φ π hX]
      exact ptOf_congr Φ π hX fun j => by
        simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
    have h2 : ptOf Φ π hX ((Algebra.TensorProduct.lmul' 𝓞 (S := L)).comp
        ((Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L).comp (S Φ n π hπ hX hker))) = -ξ Φ π hX := by
      rw [← ptOf_S Φ n π hπ hX hker]
      exact ptOf_congr Φ π hX fun j => by
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.lmul'_apply_tmul, one_mul]
    rw [h1, h2, add_neg_cancel]

private theorem comm_Δ :
    (Algebra.TensorProduct.comm 𝓞 L L).toAlgHom.comp (Δ Φ n π hπ hX hker) = Δ Φ n π hπ hX hker := by
  refine algHom_ext_pt Φ π hπ
    (mp Φ (Algebra.TensorProduct.comm 𝓞 L L).toAlgHom (a₁ Φ π hX) +
      mp Φ (Algebra.TensorProduct.comm 𝓞 L L).toAlgHom (a₂ Φ π hX))
    (a₁ Φ π hX + a₂ Φ π hX) (fun i => ?_) (fun i => Δ_πX Φ n π hπ hX hker i) ?_
  · rw [AlgHom.comp_apply, Δ_πX]
    exact apply_val_add Φ _ _ _ i
  · rw [mp_a₁, mp_a₂, add_comm, a₁, a₂]

    congr 1

@[reducible] private noncomputable def hopfAlgebra : HopfAlgebra 𝓞 L :=
  letI := bialgebra Φ n π hπ hX hker
  { antipode := (S Φ n π hπ hX hker).toLinearMap
    mul_antipode_rTensor_comul := by
      have hrT : (Algebra.TensorProduct.map (S Φ n π hπ hX hker) (AlgHom.id 𝓞 L)).toLinearMap =
          (S Φ n π hπ hX hker).toLinearMap.rTensor L := TensorProduct.ext' fun _ _ => rfl
      have h := congrArg AlgHom.toLinearMap (antipode_right Φ n π hπ hX hker)
      rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap, Algebra.TensorProduct.lmul'_toLinearMap, hrT,
        AlgHom.comp_toLinearMap] at h
      exact h
    mul_antipode_lTensor_comul := by
      have hlT : (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (S Φ n π hπ hX hker)).toLinearMap =
          (S Φ n π hπ hX hker).toLinearMap.lTensor L := TensorProduct.ext' fun _ _ => rfl
      have h := congrArg AlgHom.toLinearMap (antipode_left Φ n π hπ hX hker)
      rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap, Algebra.TensorProduct.lmul'_toLinearMap, hlT,
        AlgHom.comp_toLinearMap] at h
      exact h }

private theorem isCocomm : @Coalgebra.IsCocomm 𝓞 L _ _ _ (hopfAlgebra Φ n π hπ hX hker).toCoalgebra :=
  letI := hopfAlgebra Φ n π hπ hX hker
  ⟨congrArg AlgHom.toLinearMap (comm_Δ Φ n π hπ hX hker)⟩

private theorem comul_πX (i : Fin d) :
    (hopfAlgebra Φ n π hπ hX hker).comul (π (X i)) =
      MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L)))
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : L)) (fun j => (1 : L) ⊗ₜ[𝓞] π (X j))) (Φ.toPowerSeries i) := by
  change Δ Φ n π hπ hX hker (π (X i)) = _
  rw [Δ_πX]
  rfl

private theorem counit_π (G : MvPowerSeries (Fin d) 𝓞) :
    (hopfAlgebra Φ n π hπ hX hker).counit (π G) = MvPowerSeries.constantCoeff G :=
  ε_π Φ n π hπ hker G

end Axioms

end Level

section Main

variable {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm] (n : ℕ)
  {M : Type u} [CommRing M] [Algebra 𝓞 M] [Module.Finite 𝓞 M] [Module.Free 𝓞 M]
  (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] M) (hπ : Surjective π) (hX : ∀ i, IsNilpotent (π (X i)))
  (hker : RingHom.ker π = Ideal.span (Set.range (Φ.nthSeries n)))

include hπ hX hker in
private theorem main :
    ∃ (L : Type u) (_ : CommRing L) (_ : HopfAlgebra 𝓞 L) (_ : Coalgebra.IsCocomm 𝓞 L)
      (_ : Module.Free 𝓞 L) (_ : Module.Finite 𝓞 L) (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L),
      Function.Surjective π ∧
      RingHom.ker π = Ideal.span (Set.range (Φ.nthSeries n)) ∧
      Module.finrank 𝓞 L =
        Module.finrank 𝓞 M ∧
      (∀ i, IsNilpotent (π (X i))) ∧
      (∀ G, π G = MvFormalGroup.adicEval ((⊥ : Ideal L)) (fun i => π (X i)) G) ∧
      (∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
        MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L)))
          (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : L)) (fun j => (1 : L) ⊗ₜ[𝓞] π (X j)))
          (Φ.toPowerSeries i)) ∧
      (∀ i, Coalgebra.counit (R := 𝓞) (π (X i)) = 0) ∧
      (∀ G, Coalgebra.counit (R := 𝓞) (π G) = MvPowerSeries.constantCoeff G) := by
  exact ⟨M, inferInstance, hopfAlgebra Φ n π hπ hX hker, isCocomm Φ n π hπ hX hker, inferInstance, inferInstance,
    π, hπ, hker, rfl, hX, π_eq_adicEval π hX, comul_πX Φ n π hπ hX hker,
    ε_πX Φ n π hπ hker, counit_π Φ n π hπ hX hker⟩

end Main

end HopfQuot

open HopfQuot in
theorem solution
    {A : Type} [CommRing A] {d : ℕ} (Φ : MvFormalGroup d A) [Φ.IsComm] (n : ℕ)
    [Module.Finite A (MvPowerSeries (Fin d) A ⧸ Ideal.span (Set.range (Φ.nthSeries n)))]
    [Module.Free A (MvPowerSeries (Fin d) A ⧸ Ideal.span (Set.range (Φ.nthSeries n)))]
    (hX : ∀ i, IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range (Φ.nthSeries n))) (X i))) :
    ∃ (L : Type) (_ : CommRing L) (_ : HopfAlgebra A L) (_ : Coalgebra.IsCocomm A L)
      (_ : Module.Free A L) (_ : Module.Finite A L) (π : MvPowerSeries (Fin d) A →ₐ[A] L),
      Function.Surjective π ∧
      RingHom.ker π = Ideal.span (Set.range (Φ.nthSeries n)) ∧
      Module.finrank A L =
        Module.finrank A (MvPowerSeries (Fin d) A ⧸ Ideal.span (Set.range (Φ.nthSeries n))) ∧
      (∀ i, IsNilpotent (π (X i))) ∧
      (∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (X i)) G) ∧
      (∀ i, Coalgebra.comul (R := A) (π (X i)) =
        MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[A] L))
          (Sum.elim (fun j => π (X j) ⊗ₜ[A] (1 : L)) (fun j => (1 : L) ⊗ₜ[A] π (X j)))
          (Φ.toPowerSeries i)) ∧
      (∀ i, Coalgebra.counit (R := A) (π (X i)) = 0) ∧
      (∀ G, Coalgebra.counit (R := A) (π G) = MvPowerSeries.constantCoeff G) := by
  exact main Φ n (Ideal.Quotient.mkₐ A (Ideal.span (Set.range (Φ.nthSeries n))))
    (Ideal.Quotient.mkₐ_surjective A _) hX (Ideal.Quotient.mkₐ_ker A _)

end S_MvFormalGroup_exists_hopfAlgebra_surjective_ker_eq_span_nthSeries_comul_eq_adicEval_bot_of_isNilpotent
end P2MW
export P2MW.S_MvFormalGroup_exists_hopfAlgebra_surjective_ker_eq_span_nthSeries_comul_eq_adicEval_bot_of_isNilpotent (solution)
