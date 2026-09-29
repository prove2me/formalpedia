-- Prove2me | solution 1 for NumberField.AdelicLevel.isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/14084b12-00da-58a0-8f7b-5ad24dc3b6a2

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_PadicHeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup

set_option autoImplicit false

noncomputable section

namespace HeckeCosetTransfer

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain

theorem natGenerator_padicPlace (p : ℕ) [Fact p.Prime] :
    Rat.HeightOneSpectrum.natGenerator (padicPlace p) = p := by
  show (Rat.HeightOneSpectrum.primesEquiv (padicPlace p) : ℕ) = p
  rw [padicPlace, Equiv.apply_symm_apply]

theorem natCast_mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    show ((n : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((n : ℕ) : 𝓞 ℚ) from (map_natCast _ n).symm]
  exact Ideal.apply_mem_of_equiv_iff.symm

theorem natCast_natGenerator_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero

theorem prime_natCast_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    Prime ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) := by
  have hcast : ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) =
      Rat.ringOfIntegersEquiv.symm ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) :=
    (map_natCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm
  rw [hcast]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
    (Nat.prime_iff_prime_int.mp (Rat.HeightOneSpectrum.prime_natGenerator v))

theorem asIdeal_eq_span_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)} := by
  have hmax : (Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (natCast_natGenerator_ne_zero v)).mpr (prime_natCast_natGenerator v)).isMaximal
      ((Ideal.span_singleton_eq_bot (α := 𝓞 ℚ)).not.mpr (natCast_natGenerator_ne_zero v))
  exact (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr
    ((natCast_mem_asIdeal_iff v _).mpr dvd_rfl))).symm

theorem asIdeal_padicPlace (p : ℕ) [Fact p.Prime] :
    (padicPlace p).asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)} := by
  rw [asIdeal_eq_span_natGenerator, natGenerator_padicPlace]

theorem valued_natCast (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = v.intValuation ((n : ℕ) : 𝓞 ℚ) := by
  have h1 : ((n : ℕ) : v.adicCompletion ℚ) = algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ) :=
    (map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n).symm
  have h2 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ)) = v.valuation ℚ ((n : ℕ) : ℚ) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h1, h2, show ((n : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((n : ℕ) : 𝓞 ℚ) from (map_natCast (algebraMap (𝓞 ℚ) ℚ) _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]

theorem valued_natCast_self (p : ℕ) [hp : Fact p.Prime] :
    Valued.v ((p : ℕ) : (padicPlace p).adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [valued_natCast]
  exact HeightOneSpectrum.intValuation_singleton (v := padicPlace p) (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    (asIdeal_padicPlace p)

theorem natCast_self_ne_zero (p : ℕ) [hp : Fact p.Prime] :
    ((p : ℕ) : (padicPlace p).adicCompletion ℚ) ≠ 0 := by
  intro h
  have h1 := valued_natCast_self p
  rw [h, Valuation.map_zero] at h1
  exact WithZero.exp_ne_zero h1.symm

def natUnit (p : ℕ) [Fact p.Prime] : ((padicPlace p).adicCompletion ℚ)ˣ :=
  Units.mk0 _ (natCast_self_ne_zero p)

theorem coe_natUnit (p : ℕ) [Fact p.Prime] :
    ((natUnit p : ((padicPlace p).adicCompletion ℚ)ˣ) : (padicPlace p).adicCompletion ℚ)
      = ((p : ℕ) : (padicPlace p).adicCompletion ℚ) := rfl

theorem gl_ext_of_arch_fin {x y : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : glArch (𝓞 ℚ) ℚ x = glArch (𝓞 ℚ) ℚ y) (h₂ : glFin (𝓞 ℚ) ℚ x = glFin (𝓞 ℚ) ℚ y) : x = y := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ ?_)
  · exact congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) a b) h₁
  · exact congrArg
      (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) h₂

theorem coe_finComponent (w : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((finComponent (𝓞 ℚ) ℚ w g) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
      = (finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  rw [finComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply]

theorem glEq_of_forall_finComponent_eq {g h : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (H : ∀ w : HeightOneSpectrum (𝓞 ℚ), finComponent (𝓞 ℚ) ℚ w g = finComponent (𝓞 ℚ) ℚ w h) :
    g = h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => congrFun (congrFun ?_ i) j
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
  rw [← coe_finComponent w g, ← coe_finComponent w h, H w]

theorem glArch_heckeGenAt (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) :
    glArch (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ v t) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glArch_apply, heckeGenAt_fst, Units.val_one]

section Level

variable {N : ℕ} (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

abbrev levelU (N : ℕ) : Subgroup (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
  levelOne (𝓞 ℚ) ℚ (ratLevel N) ⊓ finiteAdelicGL2Subgroup ℚ

theorem mem_levelU_iff (T : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    T ∈ levelU N ↔ glFin (𝓞 ℚ) ℚ T ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N) ∧ glArch (𝓞 ℚ) ℚ T = 1 :=
  Iff.rfl

theorem padicToAdelic_mem_levelU (hN : N ≠ 0) (hℓN : ¬ ℓ ∣ N) {k : GL (Fin 2) ℚ_[ℓ]}
    (hk : k ∈ LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ]) : padicToAdelic ℓ k ∈ levelU N := by
  obtain ⟨y, rfl⟩ := hk
  refine ⟨?_, glArch_padicToAdelic ℓ _⟩
  exact padicToAdelic_mem_levelOne ℓ hN (by rw [Nat.factorization_eq_zero_of_not_dvd hℓN])
    (n := 0) ⟨y, rfl, by simp, by simp⟩

theorem padicGL_mem_localLevelOne_of_mem (hN : N ≠ 0) (hℓN : ¬ ℓ ∣ N) {k : GL (Fin 2) ℚ_[ℓ]}
    (hk : k ∈ LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ]) :
    padicGL ℓ k ∈ localLevelOne (𝓞 ℚ) ℚ (padicPlace ℓ) (ratLevel N) := by
  obtain ⟨y, rfl⟩ := hk
  exact padicGL_mem_localLevelOne ℓ hN (by rw [Nat.factorization_eq_zero_of_not_dvd hℓN])
    (n := 0) ⟨y, rfl, by simp, by simp⟩

theorem mapMatrix_injective {A B : Type*} [Semiring A] [Semiring B] {f : A →+* B}
    (hf : Function.Injective f) :
    Function.Injective ((RingHom.mapMatrix f : Matrix (Fin 2) (Fin 2) A →+* _)) := fun M M' h => by
  ext i j
  exact hf (by simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun h i) j)

theorem exists_glMap_eq {R : Type*} [CommRing R] {K : Type*} [CommRing K]
    (f : R →+* K) (hf : Function.Injective f) (x : GL (Fin 2) K)
    (hx : ∀ i j, ∃ r, f r = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (hx' : ∀ i j, ∃ r, f r = ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) :
    ∃ c : GL (Fin 2) R, Matrix.GeneralLinearGroup.map (n := Fin 2) f c = x := by
  set M : Matrix (Fin 2) (Fin 2) R := fun i j => Classical.choose (hx i j) with hM
  set M' : Matrix (Fin 2) (Fin 2) R := fun i j => Classical.choose (hx' i j)
  have hMim : f.mapMatrix M = (x : Matrix (Fin 2) (Fin 2) K) :=
    Matrix.ext fun i j => Classical.choose_spec (hx i j)
  have hM'im : f.mapMatrix M' = ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    Matrix.ext fun i j => Classical.choose_spec (hx' i j)
  have hinj : Function.Injective ((RingHom.mapMatrix f : Matrix (Fin 2) (Fin 2) R →+* _)) :=
    mapMatrix_injective hf
  have hMM' : M * M' = 1 := hinj (by
    rw [map_mul, hMim, hM'im, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hM'M : M' * M = 1 := hinj (by
    rw [map_mul, hM'im, hMim, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨M, M', hMM', hM'M⟩, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrFun (congrFun hMim i) j

theorem exists_finComponent_eq_padicGL {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N)) :
    ∃ c ∈ LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ], finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) u = padicGL ℓ c := by
  obtain ⟨hu₁, hu₂⟩ := mem_finiteLevelOne_iff.mp hu
  set cq : GL (Fin 2) ℚ_[ℓ] := Matrix.GeneralLinearGroup.map (n := Fin 2)
    (padicRingEquiv ℓ).symm.toRingHom (finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) u) with hcq
  have hcq_inv : padicGL ℓ cq = finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) u :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [padicGL_apply, hcq, Matrix.GeneralLinearGroup.map_apply]
      exact RingEquiv.apply_symm_apply _ _
  have hex : ∀ (e : GL (Fin 2) ((padicPlace ℓ).adicCompletion ℚ)),
      (∀ i j, (e : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace ℓ).adicCompletionIntegers ℚ) →
      ∀ i j, ∃ r : ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ] r
        = (Matrix.GeneralLinearGroup.map (n := Fin 2) (padicRingEquiv ℓ).symm.toRingHom e
            : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) i j := fun e he i j => by
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact ⟨⟨_, (norm_le_one_iff_mem ℓ _).mpr
      ((RingEquiv.apply_symm_apply (padicRingEquiv ℓ) _).symm ▸ he i j)⟩,
      (PadicInt.algebraMap_apply _).trans rfl⟩
  have hmem : ∀ i j, (finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) u
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace ℓ).adicCompletionIntegers ℚ := fun i j => by
    rw [finComponent_apply]; exact hu₁.integral i j (padicPlace ℓ)
  have hmem' : ∀ i j, (finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) u⁻¹
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace ℓ).adicCompletionIntegers ℚ := fun i j => by
    rw [finComponent_apply]; exact hu₂.integral i j (padicPlace ℓ)
  obtain ⟨c, hc⟩ := exists_glMap_eq (algebraMap ℤ_[ℓ] ℚ_[ℓ])
    (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]) cq (hcq ▸ hex _ hmem)
    (by rw [hcq, ← map_inv, ← map_inv]; exact hex _ hmem')
  exact ⟨_, ⟨c, rfl⟩, hcq_inv ▸ congrArg (padicGL ℓ) hc.symm⟩

theorem mem_finiteLevelOne_of_off_of_at {G y : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hy : y ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N))
    (hoff : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ padicPlace ℓ →
      finComponent (𝓞 ℚ) ℚ w G = finComponent (𝓞 ℚ) ℚ w y)
    (hat : finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) G ∈ localLevelOne (𝓞 ℚ) ℚ (padicPlace ℓ) (ratLevel N)) :
    G ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N) := by

  have key : ∀ {G' y' : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)},
      IsLevelOneMatrix (𝓞 ℚ) ℚ (ratLevel N) (y' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) →
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ padicPlace ℓ →
        finComponent (𝓞 ℚ) ℚ w G' = finComponent (𝓞 ℚ) ℚ w y') →
      IsLocalLevelOne (𝓞 ℚ) ℚ (padicPlace ℓ) (ratLevel N)
        ((finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) G' : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) →
      IsLevelOneMatrix (𝓞 ℚ) ℚ (ratLevel N) (G' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    intro G' y' hy' hoff' hat'
    have hentry : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (i j : Fin 2),
        (G' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j w
          = ((finComponent (𝓞 ℚ) ℚ w G' : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j :=
      fun w i j => (finComponent_apply (𝓞 ℚ) ℚ w G' i j).symm
    have hoffentry : ∀ (w : HeightOneSpectrum (𝓞 ℚ)), w ≠ padicPlace ℓ → ∀ i j : Fin 2,
        (G' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j w
          = (y' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j w := by
      intro w hw i j
      rw [hentry, hoff' w hw, finComponent_apply]
    refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
    · by_cases hw : w = padicPlace ℓ
      · subst hw; rw [hentry]; exact hat'.integral i j
      · rw [hoffentry w hw]; exact hy'.integral i j w
    · by_cases hw : w = padicPlace ℓ
      · subst hw; rw [hentry]; exact hat'.lowerLeft
      · rw [hoffentry w hw]; exact hy'.lowerLeft w
    · by_cases hw : w = padicPlace ℓ
      · subst hw; rw [coe_sub_apply, coe_one_apply, hentry]; exact hat'.lowerRight
      · rw [coe_sub_apply, coe_one_apply, hoffentry w hw, ← coe_one_apply (R := 𝓞 ℚ) (K := ℚ) w,
          ← coe_sub_apply]
        exact hy'.lowerRight w
  obtain ⟨hy₁, hy₂⟩ := mem_finiteLevelOne_iff.mp hy
  obtain ⟨hat₁, hat₂⟩ := (mem_localLevelOne_iff (𝓞 ℚ) ℚ (padicPlace ℓ) _).mp hat
  refine mem_finiteLevelOne_iff.mpr ⟨key hy₁ hoff hat₁, key hy₂ (fun w hw => ?_) ?_⟩
  · rw [map_inv, map_inv, hoff w hw]
  · rw [map_inv]; exact hat₂

theorem mem_levelU_of_arch_off_at (hN : N ≠ 0) (hℓN : ¬ ℓ ∣ N) {T y : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hy : y ∈ levelU N) (harch : glArch (𝓞 ℚ) ℚ T = 1)
    (hoff : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ padicPlace ℓ →
      finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ T) = finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ y))
    {k : GL (Fin 2) ℚ_[ℓ]} (hk : k ∈ LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ])
    (hat : finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) (glFin (𝓞 ℚ) ℚ T) = padicGL ℓ k) :
    T ∈ levelU N := by
  refine ⟨?_, harch⟩
  show glFin (𝓞 ℚ) ℚ T ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N)
  refine mem_finiteLevelOne_of_off_of_at ℓ hy.1 hoff ?_
  rw [hat]
  exact padicGL_mem_localLevelOne_of_mem ℓ hN hℓN hk

end Level

section Gen

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem padicToAdelic_padicDiagP :
    padicToAdelic ℓ (HeckeIntegralSeam.padicDiagP ℓ) = heckeGenAt (𝓞 ℚ) ℚ (padicPlace ℓ) (natUnit ℓ) := by
  refine gl_ext_of_arch_fin ?_ ?_
  · rw [glArch_padicToAdelic, glArch_heckeGenAt]
  · rw [glFin_padicToAdelic]
    refine glEq_of_forall_finComponent_eq fun w => ?_
    by_cases hw : w = padicPlace ℓ
    · subst hw
      rw [finComponent_padicToFinAdelic_self]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [padicGL_apply, finComponent_apply, glFin_apply, heckeGenAt_snd_apply_self, coe_natUnit]
      change padicRingEquiv ℓ ((LocalGL2.diagPi (K := ℚ_[ℓ]) (ℓ : ℤ_[ℓ])
        (HeckeIntegralSeam.algebraMap_natCast_p_ne_zero ℓ) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) i j) = _
      rw [LocalGL2.coe_diagPi]
      fin_cases i <;> fin_cases j
      · simp [map_natCast]
      · simp
      · simp
      · simp
    · rw [finComponent_padicToFinAdelic_of_ne ℓ _ hw]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [finComponent_apply, glFin_apply, heckeGenAt_snd_apply_of_ne _ hw, Units.val_one]

theorem heckeGen_inv_mul_padicToAdelic_padicDiagP_mem {N : ℕ} :
    (heckeGen (𝓞 ℚ) ℚ (padicPlace ℓ))⁻¹ * padicToAdelic ℓ (HeckeIntegralSeam.padicDiagP ℓ) ∈ levelU N := by
  rw [padicToAdelic_padicDiagP]
  refine ⟨heckeGen_inv_mul_heckeGenAt_mem_levelOne _ ?_ _, ?_⟩
  · rw [coe_natUnit]; exact valued_natCast_self ℓ
  · show glArch (𝓞 ℚ) ℚ _ = 1
    rw [map_mul, map_inv, heckeGen, glArch_heckeGenAt, glArch_heckeGenAt, inv_one, one_mul]

end Gen

section Transfer

variable {N : ℕ} (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem finComponent_conj_of_ne (u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (x x' : GL (Fin 2) ℚ_[ℓ])
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ padicPlace ℓ) :
    finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ ((u * padicToAdelic ℓ x)⁻¹ * padicToAdelic ℓ x'))
      = finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ u⁻¹) := by
  simp only [map_mul, map_inv, glFin_padicToAdelic, finComponent_padicToFinAdelic_of_ne ℓ _ hw, mul_one]

theorem finComponent_conj_self {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {c : GL (Fin 2) ℚ_[ℓ]}
    (hc : finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) (glFin (𝓞 ℚ) ℚ u) = padicGL ℓ c) (x x' : GL (Fin 2) ℚ_[ℓ]) :
    finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) (glFin (𝓞 ℚ) ℚ ((u * padicToAdelic ℓ x)⁻¹ * padicToAdelic ℓ x'))
      = padicGL ℓ ((c * x)⁻¹ * x') := by
  simp only [map_mul, map_inv, glFin_padicToAdelic, finComponent_padicToFinAdelic_self, hc]

theorem glArch_conj {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : glArch (𝓞 ℚ) ℚ u = 1) (x x' : GL (Fin 2) ℚ_[ℓ]) :
    glArch (𝓞 ℚ) ℚ ((u * padicToAdelic ℓ x)⁻¹ * padicToAdelic ℓ x') = 1 := by
  rw [map_mul, map_inv, map_mul, hu, glArch_padicToAdelic, glArch_padicToAdelic, one_mul, inv_one, one_mul]

theorem isHeckeCosetSystem_transfer (hN : N ≠ 0) (hℓN : ¬ ℓ ∣ N)
    {ι : Type*} (α : ι → GL (Fin 2) ℚ_[ℓ])
    (hα : HeckeIntegralSeam.IsHeckeCosetSystem (LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ])
      (HeckeIntegralSeam.padicDiagP ℓ) α) :
    HeckeIntegralSeam.IsHeckeCosetSystem (levelU N) (heckeGen (𝓞 ℚ) ℚ (padicPlace ℓ))
      (fun i => padicToAdelic ℓ (α i)) := by
  set K := LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ] with hK
  set d := HeckeIntegralSeam.padicDiagP ℓ with hd
  set g := heckeGen (𝓞 ℚ) ℚ (padicPlace ℓ) with hg
  have hseam : g⁻¹ * padicToAdelic ℓ d ∈ levelU N := heckeGen_inv_mul_padicToAdelic_padicDiagP_mem ℓ
  refine ⟨fun i => ?_, fun x hx => ?_, fun i j hij => ?_⟩
  ·
    obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := HeckePair.mem_doubleCoset_iff.mp (hα.mem_doubleCoset i)
    refine HeckePair.mem_doubleCoset_iff.mpr ⟨padicToAdelic ℓ k₁, padicToAdelic_mem_levelU ℓ hN hℓN hk₁,
      (g⁻¹ * padicToAdelic ℓ d) * padicToAdelic ℓ k₂,
      mul_mem hseam (padicToAdelic_mem_levelU ℓ hN hℓN hk₂), ?_⟩
    show padicToAdelic ℓ k₁ * g * ((g⁻¹ * padicToAdelic ℓ d) * padicToAdelic ℓ k₂) = padicToAdelic ℓ (α i)
    rw [← hk, map_mul, map_mul]
    group
  ·
    obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    obtain ⟨c, hcK, hc⟩ := exists_finComponent_eq_padicGL ℓ (mem_levelOne_iff.mp hu.1)
    have hcd : c * d ∈ HeckePair.doubleCoset K d :=
      HeckePair.mem_doubleCoset_iff.mpr ⟨c, hcK, 1, one_mem _, mul_one _⟩
    obtain ⟨i, hi⟩ := hα.covers (c * d) hcd
    refine ⟨i, ?_⟩
    have h1 : (QuotientGroup.mk (u * g * u') : _ ⧸ levelU N) = QuotientGroup.mk (u * padicToAdelic ℓ d) := by
      rw [QuotientGroup.mk_mul_of_mem _ hu', show u * padicToAdelic ℓ d = u * g * (g⁻¹ * padicToAdelic ℓ d) by group,
        QuotientGroup.mk_mul_of_mem _ hseam]
    rw [h1]
    refine QuotientGroup.eq.mpr ?_
    have hloc : (c * d)⁻¹ * α i ∈ K := QuotientGroup.eq.mp hi
    exact mem_levelU_of_arch_off_at ℓ hN hℓN (inv_mem hu) (glArch_conj ℓ hu.2 _ _)
      (fun w hw => finComponent_conj_of_ne ℓ u d (α i) hw) hloc (finComponent_conj_self ℓ hc d (α i))
  ·
    have hmem : (padicToAdelic ℓ (α i))⁻¹ * padicToAdelic ℓ (α j) ∈ levelU N := QuotientGroup.eq.mp hij
    rw [← map_inv, ← map_mul] at hmem
    obtain ⟨c, hcK, hc⟩ := exists_finComponent_eq_padicGL ℓ (mem_levelOne_iff.mp hmem.1)
    rw [glFin_padicToAdelic, finComponent_padicToFinAdelic_self] at hc
    have hloc : (α i)⁻¹ * α j ∈ K := by
      rw [padicGL_injective ℓ hc]; exact hcK
    exact hα.mk_injective (QuotientGroup.eq.mpr hloc)

end Transfer

end HeckeCosetTransfer

end

open HeckeCosetTransfer in
theorem solution
    {N : ℕ} (hN : N ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    {ι : Type*} (α : ι → GL (Fin 2) ℚ_[ℓ])
    (hα : HeckeIntegralSeam.IsHeckeCosetSystem (LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ])
      (HeckeIntegralSeam.padicDiagP ℓ) α) :
    HeckeIntegralSeam.IsHeckeCosetSystem
      (NumberField.AdelicLevel.levelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel N) ⊓
        AutomorphicForm.finiteAdelicGL2Subgroup ℚ)
      (NumberField.AdelicLevel.heckeGen (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace ℓ))
      (fun i => AdelicDock.padicToAdelic ℓ (α i)) :=
  isHeckeCosetSystem_transfer ℓ hN hℓN α hα

end S_NumberField_AdelicLevel_isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup
end P2MW
export P2MW.S_NumberField_AdelicLevel_isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup (solution)
