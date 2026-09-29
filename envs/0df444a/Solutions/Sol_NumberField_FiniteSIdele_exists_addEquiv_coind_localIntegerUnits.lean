-- Prove2me | solution 1 for NumberField.FiniteSIdele.exists_addEquiv_coind_localIntegerUnits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4118ea02-982f-5e54-a8a0-4cc4bcad63b9

import Mathlib
import Definitions.Def_NumberField_FiniteSIdeleModule
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_NumberField_PlaceTransport_transport_one
import Theorems.Thm_NumberField_PlaceTransport_transport_trans_transport
import Theorems.Thm_NumberField_PlaceTransport_transport_eq_actRingEquiv
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Theorems.Thm_NumberField_PlaceTransport_under_smul
import Theorems.Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_FiniteSIdele_exists_addEquiv_coind_localIntegerUnits

set_option autoImplicit false

namespace P2mS26FHI

open NumberField NumberField.PlaceTransport IsDedekindDomain
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

section general

variable {E K : Type} [Field E] [Field K] [NumberField K] [Algebra E K]

theorem transportIntegerUnits_congr {σ τ : K ≃ₐ[E] K} (e : σ = τ) {w w' : HeightOneSpectrum (𝓞 K)} (h₁ : σ • w = w') (h₂ : τ • w = w')
    (u : (w.adicCompletionIntegers K)ˣ) : transportIntegerUnits σ h₁ u = transportIntegerUnits τ h₂ u := by
  subst e; rfl

theorem transportIntegerUnits_trans (σ τ : K ≃ₐ[E] K) {w w' w'' : HeightOneSpectrum (𝓞 K)} (h₁ : τ • w = w') (h₂ : σ • w' = w'')
    (h₃ : (σ * τ) • w = w'') (u : (w.adicCompletionIntegers K)ˣ) :
    transportIntegerUnits σ h₂ (transportIntegerUnits τ h₁ u) = transportIntegerUnits (σ * τ) h₃ u := by
  apply Units.ext; apply Subtype.ext
  change transport σ h₂ (transport τ h₁ ((u : w.adicCompletionIntegers K) : w.adicCompletion K))
    = transport (σ * τ) h₃ ((u : w.adicCompletionIntegers K) : w.adicCompletion K)
  rw [← NumberField.PlaceTransport.transport_trans_transport E K σ τ h₁ h₂ h₃]
  rfl

theorem transportIntegerUnits_one {w : HeightOneSpectrum (𝓞 K)} (h : (1 : K ≃ₐ[E] K) • w = w) (u : (w.adicCompletionIntegers K)ˣ) :
    transportIntegerUnits (1 : K ≃ₐ[E] K) h u = u := by
  apply Units.ext; apply Subtype.ext
  change transport (1 : K ≃ₐ[E] K) h ((u : w.adicCompletionIntegers K) : w.adicCompletion K) = ((u : w.adicCompletionIntegers K) : w.adicCompletion K)
  rw [NumberField.PlaceTransport.transport_one E K w h]
  rfl

theorem transportIntegerUnits_eq_smul {w : HeightOneSpectrum (𝓞 K)} (d : PlaceDecomp.decomp E K w) (h : (d : K ≃ₐ[E] K) • w = w)
    (u : (w.adicCompletionIntegers K)ˣ) : transportIntegerUnits (d : K ≃ₐ[E] K) h u = d • u := by
  apply Units.ext; apply Subtype.ext
  change transport (d : K ≃ₐ[E] K) h ((u : w.adicCompletionIntegers K) : w.adicCompletion K)
    = (((d • u : (w.adicCompletionIntegers K)ˣ) : w.adicCompletionIntegers K) : w.adicCompletion K)
  rw [NumberField.PlaceTransport.transport_eq_actRingEquiv E K w d h, ← PlaceDecomp.smul_def]
  rfl

theorem decomp_smul {w : HeightOneSpectrum (𝓞 K)} (d : PlaceDecomp.decomp E K w) : (d : K ≃ₐ[E] K) • w = w := by
  have hd : (d : K ≃ₐ[E] K) ∈ MulAction.stabilizer (K ≃ₐ[E] K) w := by
    rw [NumberField.PlaceTransport.stabilizer_eq_decomp E K w]; exact d.2
  exact hd

theorem mem_decomp_of_smul_eq {w : HeightOneSpectrum (𝓞 K)} {σ : K ≃ₐ[E] K} (h : σ • w = w) : σ ∈ PlaceDecomp.decomp E K w := by
  rw [← NumberField.PlaceTransport.stabilizer_eq_decomp E K w]; exact h

end general

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

abbrev Idx (v : HeightOneSpectrum (𝓞 E)) : Type := {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 E) = v}

noncomputable abbrev Cv (v : HeightOneSpectrum (𝓞 E)) : Rep ℤ (K ≃ₐ[E] K) :=
  Rep.coind (FiniteSIdele.D E K v).subtype (FiniteSIdele.localIntegerUnits E K v)

theorem under_above (v : HeightOneSpectrum (𝓞 E)) : (PlaceAbove.above E K v).under (𝓞 E) = v :=
  HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal]; exact PlaceAbove.comap_above E K v)

variable {E K}
variable (v : HeightOneSpectrum (𝓞 E))

noncomputable def fval (f : Cv E K v) (x : K ≃ₐ[E] K) : ((PlaceAbove.above E K v).adicCompletionIntegers K)ˣ := Additive.toMul (f.1 x)

theorem fval_ρ (g : K ≃ₐ[E] K) (f : Cv E K v) (x : K ≃ₐ[E] K) : fval v ((Cv E K v).ρ g f) x = fval v f (x * g) := rfl

theorem fval_add (f₁ f₂ : Cv E K v) (x : K ≃ₐ[E] K) : fval v (f₁ + f₂) x = fval v f₁ x * fval v f₂ x := rfl

theorem coind_mem (f : Cv E K v) (d : FiniteSIdele.D E K v) (x : K ≃ₐ[E] K) :
    fval v f ((d : K ≃ₐ[E] K) * x) = d • fval v f x :=
  congrArg Additive.toMul ((Representation.mem_coindV _ _ _).1 f.2 d x)

omit [NumberField E] in

theorem transportIntegerUnits_congr_idx (u : Π w : Idx E K v, (w.1.adicCompletionIntegers K)ˣ) {i₁ i₂ : Idx E K v} (e : i₁ = i₂)
    (σ : K ≃ₐ[E] K) {t : HeightOneSpectrum (𝓞 K)} (h₁ : σ • i₁.1 = t) (h₂ : σ • i₂.1 = t) :
    transportIntegerUnits σ h₁ (u i₁) = transportIntegerUnits σ h₂ (u i₂) := by
  subst e; rfl

omit [NumberField E] in
theorem transportIntegerUnits_one_idx (u : Π w : Idx E K v, (w.1.adicCompletionIntegers K)ˣ) {i₁ i₂ : Idx E K v} (e : i₁ = i₂)
    (h : (1 : K ≃ₐ[E] K) • i₁.1 = i₂.1) : transportIntegerUnits (1 : K ≃ₐ[E] K) h (u i₁) = u i₂ := by
  subst e
  exact transportIntegerUnits_one h (u i₁)

theorem indep (f : Cv E K v) (x y : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K))
    (hx : x⁻¹ • PlaceAbove.above E K v = w) (hy : y⁻¹ • PlaceAbove.above E K v = w) :
    transportIntegerUnits y⁻¹ hy (fval v f y) = transportIntegerUnits x⁻¹ hx (fval v f x) := by
  have hd : y * x⁻¹ ∈ FiniteSIdele.D E K v :=
    mem_decomp_of_smul_eq (by rw [mul_smul, hx, ← hy, smul_inv_smul])
  obtain ⟨d, rfl⟩ : ∃ d : FiniteSIdele.D E K v, (d : K ≃ₐ[E] K) * x = y :=
    ⟨⟨y * x⁻¹, hd⟩, inv_mul_cancel_right y x⟩
  have hd1 : ((d⁻¹ : FiniteSIdele.D E K v) : K ≃ₐ[E] K) • PlaceAbove.above E K v = PlaceAbove.above E K v :=
    decomp_smul d⁻¹
  rw [coind_mem, transportIntegerUnits_congr (show ((d : K ≃ₐ[E] K) * x)⁻¹ =
        x⁻¹ * ((d⁻¹ : FiniteSIdele.D E K v) : K ≃ₐ[E] K) by rw [mul_inv_rev]; rfl) hy
      (by rw [mul_smul]; exact (congrArg (x⁻¹ • ·) hd1).trans hx),
    ← transportIntegerUnits_trans x⁻¹ ((d⁻¹ : FiniteSIdele.D E K v) : K ≃ₐ[E] K) hd1 hx,
    transportIntegerUnits_eq_smul, inv_smul_smul]

theorem mem_idx (x : K ≃ₐ[E] K) : (x⁻¹ • PlaceAbove.above E K v).under (𝓞 E) = v :=
  (NumberField.PlaceTransport.under_smul E K x⁻¹ _).trans (under_above E K v)

noncomputable def bwdFun (u : Π w : Idx E K v, (w.1.adicCompletionIntegers K)ˣ) :
    (K ≃ₐ[E] K) → Additive ((PlaceAbove.above E K v).adicCompletionIntegers K)ˣ :=
  fun x => Additive.ofMul (transportIntegerUnits x (smul_inv_smul x (PlaceAbove.above E K v)) (u ⟨x⁻¹ • PlaceAbove.above E K v, mem_idx v x⟩))

theorem bwdFun_apply (u : Π w : Idx E K v, (w.1.adicCompletionIntegers K)ˣ) (x : K ≃ₐ[E] K) :
    Additive.toMul (bwdFun v u x)
      = transportIntegerUnits x (smul_inv_smul x (PlaceAbove.above E K v)) (u ⟨x⁻¹ • PlaceAbove.above E K v, mem_idx v x⟩) := rfl

theorem bwdFun_mem (u : Π w : Idx E K v, (w.1.adicCompletionIntegers K)ˣ) :
    bwdFun v u ∈ Representation.coindV (FiniteSIdele.D E K v).subtype (FiniteSIdele.localIntegerUnits E K v).ρ := by
  refine (Representation.mem_coindV _ _ _).2 fun d x => ?_
  apply Additive.toMul.injective
  change Additive.toMul (bwdFun v u ((d : K ≃ₐ[E] K) * x)) = d • Additive.toMul (bwdFun v u x)
  have hidx : (⟨((d : K ≃ₐ[E] K) * x)⁻¹ • PlaceAbove.above E K v, mem_idx v ((d : K ≃ₐ[E] K) * x)⟩ : Idx E K v) =
      ⟨x⁻¹ • PlaceAbove.above E K v, mem_idx v x⟩ := by
    apply Subtype.ext
    change ((d : K ≃ₐ[E] K) * x)⁻¹ • PlaceAbove.above E K v = x⁻¹ • PlaceAbove.above E K v
    rw [mul_inv_rev, mul_smul]
    exact congrArg (x⁻¹ • ·) (decomp_smul d⁻¹)
  rw [bwdFun_apply, bwdFun_apply, transportIntegerUnits_congr_idx v u hidx ((d : K ≃ₐ[E] K) * x) _
      (by rw [mul_smul, smul_inv_smul]; exact decomp_smul d),
    ← transportIntegerUnits_trans (d : K ≃ₐ[E] K) x (smul_inv_smul x _) (decomp_smul d), transportIntegerUnits_eq_smul]

noncomputable def bwd (u : Π w : Idx E K v, (w.1.adicCompletionIntegers K)ˣ) : Cv E K v := ⟨bwdFun v u, bwdFun_mem v u⟩

section
variable [IsGalois E K]

theorem exists_smul_eq (w : Idx E K v) : ∃ x : K ≃ₐ[E] K, x • w.1 = PlaceAbove.above E K v := by
  have hmem : PlaceAbove.above E K v ∈ MulAction.orbit (K ≃ₐ[E] K) w.1 := by
    rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq E K w.1]
    exact (under_above E K v).trans w.2.symm
  exact MulAction.mem_orbit_iff.1 hmem

noncomputable def sel (w : Idx E K v) : K ≃ₐ[E] K := (exists_smul_eq v w).choose

theorem sel_smul (w : Idx E K v) : sel v w • w.1 = PlaceAbove.above E K v := (exists_smul_eq v w).choose_spec

theorem inv_sel_smul (w : Idx E K v) : (sel v w)⁻¹ • PlaceAbove.above E K v = w.1 := inv_smul_eq_of_smul_eq (sel_smul v w)

noncomputable def fwd (f : Cv E K v) : Π w : Idx E K v, (w.1.adicCompletionIntegers K)ˣ :=
  fun w => transportIntegerUnits (sel v w)⁻¹ (inv_sel_smul v w) (fval v f (sel v w))

theorem fwd_eq (f : Cv E K v) (w : Idx E K v) (y : K ≃ₐ[E] K) (hy : y • w.1 = PlaceAbove.above E K v) :
    fwd v f w = transportIntegerUnits y⁻¹ (inv_smul_eq_of_smul_eq hy) (fval v f y) :=
  (indep v f y (sel v w) w.1 (inv_smul_eq_of_smul_eq hy) (inv_sel_smul v w))

theorem fwd_add (f₁ f₂ : Cv E K v) (w : Idx E K v) : fwd v (f₁ + f₂) w = fwd v f₁ w * fwd v f₂ w := by
  change transportIntegerUnits _ _ (fval v (f₁ + f₂) (sel v w)) = _
  rw [fval_add, map_mul]
  rfl

theorem fwd_ρ (g : K ≃ₐ[E] K) (f : Cv E K v) (w w' : Idx E K v) (h : g • w'.1 = w.1) :
    fwd v ((Cv E K v).ρ g f) w = transportIntegerUnits g h (fwd v f w') := by
  have hy : (sel v w * g) • w'.1 = PlaceAbove.above E K v := by rw [mul_smul, h, sel_smul]
  rw [fwd_eq v f w' (sel v w * g) hy, transportIntegerUnits_trans g (sel v w * g)⁻¹ (inv_smul_eq_of_smul_eq hy) h
      (by rw [mul_inv_rev, mul_inv_cancel_left]; exact inv_sel_smul v w),
    transportIntegerUnits_congr (show g * (sel v w * g)⁻¹ = (sel v w)⁻¹ by rw [mul_inv_rev, mul_inv_cancel_left]) _ (inv_sel_smul v w)]
  rfl

theorem fwd_bwd (u : Π w : Idx E K v, (w.1.adicCompletionIntegers K)ˣ) (w : Idx E K v) : fwd v (bwd v u) w = u w := by
  have hidx : (⟨(sel v w)⁻¹ • PlaceAbove.above E K v, mem_idx v (sel v w)⟩ : Idx E K v) = w := Subtype.ext (inv_sel_smul v w)
  change transportIntegerUnits (sel v w)⁻¹ (inv_sel_smul v w) (Additive.toMul (bwdFun v u (sel v w))) = u w
  rw [bwdFun_apply, transportIntegerUnits_trans (sel v w)⁻¹ (sel v w) (smul_inv_smul (sel v w) _) (inv_sel_smul v w)
      (by rw [inv_mul_cancel, one_smul]; exact inv_sel_smul v w),
    transportIntegerUnits_congr (inv_mul_cancel (sel v w)) _ (by rw [one_smul]; exact inv_sel_smul v w)]
  exact transportIntegerUnits_one_idx v u hidx _

theorem bwd_fwd (f : Cv E K v) : bwd v (fwd v f) = f := by
  apply Subtype.ext
  funext x
  apply Additive.toMul.injective
  change Additive.toMul (bwdFun v (fwd v f) x) = fval v f x
  rw [bwdFun_apply, fwd_eq v f ⟨x⁻¹ • PlaceAbove.above E K v, mem_idx v x⟩ x (smul_inv_smul x _),
    transportIntegerUnits_trans x x⁻¹ _ (smul_inv_smul x _) (by rw [mul_inv_cancel, one_smul]),
    transportIntegerUnits_congr (mul_inv_cancel x) _ (one_smul _ _), transportIntegerUnits_one]

noncomputable def equiv : Cv E K v ≃+ Additive (Π w : Idx E K v, (w.1.adicCompletionIntegers K)ˣ) where
  toFun f := Additive.ofMul (fwd v f)
  invFun a := bwd v (Additive.toMul a)
  left_inv f := bwd_fwd v f
  right_inv a := congrArg Additive.ofMul (funext (fwd_bwd v (Additive.toMul a)))
  map_add' f₁ f₂ := congrArg Additive.ofMul (funext (fwd_add v f₁ f₂))

end

end P2mS26FHI

open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

theorem solution (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsGalois E K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    ∃ e : (Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v))
          ≃+ Additive (Π w : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
                            w.under (NumberField.RingOfIntegers E) = v}, (w.1.adicCompletionIntegers K)ˣ),
      ∀ (g : K ≃ₐ[E] K) (f : Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v))
        (w w' : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
                  w.under (NumberField.RingOfIntegers E) = v})
        (h : g • w'.1 = w.1),
        Additive.toMul (e ((Rep.coind (NumberField.FiniteSIdele.D E K v).subtype
          (NumberField.FiniteSIdele.localIntegerUnits E K v)).ρ g f)) w
          = NumberField.PlaceTransport.transportIntegerUnits g h (Additive.toMul (e f) w') :=
  ⟨P2mS26FHI.equiv v, fun g f w w' h => P2mS26FHI.fwd_ρ v g f w w' h⟩

end S_NumberField_FiniteSIdele_exists_addEquiv_coind_localIntegerUnits
end P2MW
export P2MW.S_NumberField_FiniteSIdele_exists_addEquiv_coind_localIntegerUnits (solution)
