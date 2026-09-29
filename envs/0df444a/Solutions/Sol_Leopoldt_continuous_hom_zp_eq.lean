-- Prove2me | solution 1 for Leopoldt.continuous_hom_zp_eq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:43:15.45449+00:00
-- url     : https://prove2.me/submissions/2df1f4f4-5aee-4855-bce9-e98427a76f68

import Definitions.Def_LeopoldtDefect

open NumberField IsDedekindDomain Leopoldt

theorem solution (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    {f g : Multiplicative ℤ_[p] →* SemilocalUnits p K} (hf : Continuous f) (hg : Continuous g)
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g := by
  have hd : DenseRange (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[p])) :=
    PadicInt.denseRange_intCast
  have := hd.equalizer hf hg (funext fun n => by
    simp only [Function.comp_apply]
    have e : Multiplicative.ofAdd (n : ℤ_[p]) = (Multiplicative.ofAdd (1 : ℤ_[p])) ^ n := by
      rw [← ofAdd_zsmul, zsmul_one]
    rw [e, map_zpow, map_zpow, h])
  exact MonoidHom.ext (congrFun this)
